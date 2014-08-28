module EnumCheck.Enum where

import Array
import BigInt (BigInt)
import BigInt as BI
import BigInt.Convenient as I
import Either (Either(Left, Right))
import List
import Native.Error
import String
import Trampoline (Trampoline(Continue, Done), trampoline)

import EnumCheck.ExtNat (ExtNat, (+!), (-!), (*!), (/!), (<!), (<=!), (>=!))
import EnumCheck.ExtNat as EN

type Nat = BigInt
type Enum a = { size    : ExtNat
              , fromNat : Nat -> a
              }
startFuel = 100

toList : Enum a -> [a]
toList e = map e.fromNat <| BI.range BI.zero (BI.dec (EN.toBigInt e.size))

fromNat : Nat -> Enum a -> a
fromNat n e =
  if | BI.lt n BI.zero     -> Native.Error.raise "fromNat only takes nats"
     | EN.nat n >=! e.size -> Native.Error.raise <| "fromNat given index greater than size of enum\n\tSize = " ++ (BI.toString << EN.toBigInt) e.size ++ " and index = "  ++ BI.toString n
     | otherwise  -> e.fromNat n

-- | Combinators
finE : [a] -> Enum a
finE xs = let arr = Array.fromList xs
              len = Array.foldl (\_ i -> BI.inc i) BI.zero arr
          in { size = EN.nat len
             , fromNat n = Array.getOrFail (BI.toInt n) arr
             }

mapE : (a -> b) -> Enum a -> Enum b
mapE f e = { e | fromNat <- f << e.fromNat }

splitE : Nat -> Enum a -> (Enum a, Enum a)
splitE n e = (takeE n e, dropE n e)

takeE : Nat -> Enum a -> Enum a
takeE n es = { size    = EN.min (EN.nat n) es.size
             , fromNat = es.fromNat
             }

reverseE : Enum a -> Enum a
reverseE e =
  let size = EN.toBigInt e.size
      less = BI.dec size
  in { size      = e.size
     , fromNat = e.fromNat << BI.subtract less
     }

everyE : Nat -> Enum a -> Enum a
everyE n e =
  let size' = e.size /! n
      offset = BI.dec n
      f m = e.fromNat (BI.add offset (BI.multiply m n))
  in { size = size'
     , fromNat = f
     } 

dropE : Nat -> Enum a -> Enum a
dropE n es =
  let extN = EN.nat n
      f m = es.fromNat (BI.add m n)
  in { size = if | es.size >=! extN -> es.size -! extN
                 | otherwise        -> (EN.nat BI.zero)
     , fromNat = f
     }

appendE : Enum a -> Enum a -> Enum a
appendE xs ys =
    let f n = if EN.nat n <! xs.size
              then xs.fromNat n
              else ys.fromNat (BI.subtract n (EN.toBigInt xs.size))
    in { size = xs.size +! ys.size
       , fromNat = f
       }

quotRem x y = (x // y, x % y)

orE : Enum a -> Enum a -> Enum a
orE xs ys = 
    let newSize = xs.size +! ys.size
    in 
      if | xs.size == ys.size -> 
             { size = newSize
             , fromNat n = let (q,r) = BI.quotRem n I.two
                               e = if r == BI.zero then xs else ys
                           in e.fromNat q
             }
         | otherwise ->
             let (lessE, bigE, flipped) = 
                     if | xs.size <=! ys.size -> (xs, ys, False)
                        | otherwise -> (ys, xs, True)
                 (belowBigE, aboveE) = splitE (EN.toBigInt lessE.size) bigE
                 belowE = if flipped
                          then orE belowBigE lessE
                          else orE lessE belowBigE
             in appendE belowE aboveE

-- | TODO: make this fair
anyE : [Enum a] -> Enum a
anyE = foldr orE emptyE

eitherE : Enum a -> Enum b -> Enum (Either a b)
eitherE l r = orE (mapE Left l) (mapE Right r)

pickLess xs ys = if | xs.size <=! ys.size -> (xs, ys, False)
                    | otherwise -> (ys, xs, True)

pairE : Enum a -> Enum b -> Enum (a, b)
pairE xs ys =
    let newS = xs.size *! ys.size 
    in 
      if | xs.size == ys.size ->
             let fromNat' n = let flroot   = BI.flroot n
                                  diff     = n `BI.subtract` (flroot `BI.multiply` flroot)
                                  (n1, n2) = if BI.lt diff flroot
                                             then (diff, flroot)
                                             else (flroot, diff `BI.subtract` flroot)
                              in (xs.fromNat n1, ys.fromNat n2)
             in { size = newS, fromNat = fromNat' }
         | otherwise          ->
             let firstLess = xs.size <=! ys.size
                 lessSize = EN.toBigInt <| if firstLess then xs.size else ys.size
                 fromNat' n =
                   let (q, r) = BI.quotRem n lessSize
                       (n1, n2) = if firstLess
                                  then (r, q)
                                  else (q, r)
                   in (xs.fromNat n1, ys.fromNat n2)
             in { size = newS , fromNat = fromNat' }

apE : Enum (a -> b) -> Enum a -> Enum b
apE fs xs = mapE (uncurry (<|)) (pairE fs xs)

-- | The nth elt of the output lists will come from the nth input enumeration
listE : [Enum a] -> Enum [a]
listE = foldr (\hd acc -> (::) `mapE` hd `apE` acc) (finE [[]])

zipE : Enum a -> Enum b -> Enum (a, b)
zipE e1 e2 =
  let f n = (e1.fromNat n, e2.fromNat n)
  in { size = EN.min e1.size e2.size
     , fromNat = f
     }

fixE : (Enum a -> Enum a) -> Enum a
fixE f = let e () = f (fixE f)
         in { size = EN.inf, fromNat n = (e ()).fromNat n }

-- | Base enumerators
natE : Enum BigInt
natE = { size = EN.inf, fromNat = identity }

smallNatE : Enum Int
smallNatE = BI.toInt `mapE` natE

emptyE : Enum a
emptyE = { size = EN.zero, fromNat x = Native.Error.raise "Enum.elm: there are no elements in emptyE!" }

boolE : Enum Bool
boolE = finE [True, False]

ordE : Enum Order
ordE = finE [LT, EQ, GT]

manyE : Enum a -> Enum [a]
manyE e = if e.size == EN.zero
          then finE [[]]
          else fixE (\lE ->
                         orE (finE [[]])
                             ((::) `mapE` e `apE` manyE e) 
                    )

-- TODO: use arrays in interpretation part once remove is fixed
permsE : [a] -> Enum [a]
permsE xs =
  let len = BI.length xs
      choices = listE << map (\x -> takeE (BI.subtract len x) natE) <| BI.range BI.zero (BI.dec len)
      permute = interp xs
  in permute `mapE` choices

interp xs is = interpret xs is []

interpret : [a] -> [BigInt] -> [a] -> [a]
interpret curXs curIs acc = case curIs of
  []      -> acc -- Possibly should be reverse acc, idk
  (i::is) -> let x = case (BI.drop i curXs) of
                   []   -> Native.Error.raise ("Enum.elm: interpret bug")
                   x::_ -> x
                 newXs = BI.remove i curXs
             in interpret newXs is (x :: acc)
