module EnumCheck.Enum where

import Array
import BigInt (BigInt)
import BigInt as BI
import Either (Either(Left, Right))
import Native.Error

import EnumCheck.ExtNat (ExtNat, (+!), (-!), (*!), (/!), (<!), (<=!), (>=!))
import EnumCheck.ExtNat as EN

type Nat = BigInt
type Enum a = { size    : ExtNat
              , fromNat : Nat -> a
              }

toList : Enum a -> [a]
toList e = map e.fromNat <| BI.range BI.zero (BI.dec (EN.toBigInt e.size))

fromNat : Nat -> Enum a -> a
fromNat n e = if | BI.lt n BI.zero     -> Native.Error.raise "fromNat only takes nats"
                 | EN.nat n >=! e.size -> Native.Error.raise "fromNat given index greater than size of enum"
                 | otherwise  -> e.fromNat n

-- | Combinators
finE : [a] -> Enum a
finE xs = let arr = Array.fromList xs
              len = Array.length arr
          in { size = EN.fromInt len
             , fromNat n = Array.getOrFail (BI.toInt n) arr
             }

mapE : (a -> b) -> Enum a -> Enum b
mapE f e = { e | fromNat <- f << e.fromNat }

splitE : Int -> Enum a -> (Enum a, Enum a)
splitE n e = (takeE n e, dropE n e)

takeE : Int -> Enum a -> Enum a
takeE n es = { size = EN.fromInt n
             , fromNat = es.fromNat
             }

everyE : Int -> Enum a -> Enum a
everyE n e =
  let natN = BI.fromInt n
  in { size = e.size /! n
     , fromNat = e.fromNat << (\m -> BI.multiply m natN)
     } 

dropE : Int -> Enum a -> Enum a
dropE n es =
  let natN = BI.fromInt n
  in { size = es.size -! EN.nat natN
     , fromNat = es.fromNat << (\x -> BI.add x natN)
     }

appendE : Enum a -> Enum a -> Enum a
appendE xs ys = { size = xs.size +! ys.size 
                , fromNat n = if EN.nat n <! xs.size
                              then xs.fromNat n
                              else ys.fromNat (BI.subtract n (EN.toBigInt xs.size))
                }

quotRem x y = (x // y, x % y)

orE : Enum a -> Enum a -> Enum a
orE xs ys = 
    let newSize = xs.size +! ys.size
    in 
      if | xs.size == ys.size -> 
             { size = newSize
             , fromNat n = let (q,r) = BI.quotRem n (BI.fromInt 2)
                               e = if r == BI.zero then xs else ys
                           in e.fromNat q
             }
         | otherwise ->
             let (lessE, bigE, flipped) = 
                     
                     if | xs.size <=! ys.size -> (xs, ys, False)
                        | otherwise -> (ys, xs, True)
                 (belowBigE, aboveE) = splitE (EN.toInt lessE.size) bigE
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
             let fromNat n = let (flroot, diff) = BI.flroot n
                                 (n1, n2) = if BI.lt diff flroot
                                            then (diff, flroot)
                                            else (flroot, diff `BI.subtract` flroot)
                             in (xs.fromNat n1, ys.fromNat n2)
             in { size = newS, fromNat = fromNat }
         | otherwise          ->
             let firstLess = xs.size <=! ys.size
                 lessSize = EN.toBigInt <| if firstLess then xs.size else ys.size
                 fromNat n =
                     let (q, r) = BI.quotRem n lessSize
                         (n1, n2) = if firstLess 
                                    then (r, q)
                                    else (q, r)
                     in (xs.fromNat n1, ys.fromNat n2)
             in { size = newS , fromNat = fromNat }

apE : Enum (a -> b) -> Enum a -> Enum b
apE fs xs = mapE (uncurry (<|)) (pairE fs xs)

-- | The nth elt of the output lists will come from the nth input enumeration
listE : [Enum a] -> Enum [a]
listE = foldr (\hd acc -> (::) `mapE` hd `apE` acc) (finE [[]])

fixE : (Enum a -> Enum a) -> Enum a
fixE f = let e () = f (fixE f)
         in { size = EN.inf, fromNat n = (e ()).fromNat n }

-- | Base enumerators
natE : Enum BigInt
natE = { size = EN.inf, fromNat = identity }

smallNatE : Enum Int
smallNatE = BI.toInt `mapE` natE

emptyE : Enum a
emptyE = { size = EN.zero, fromNat x = head [] }

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

remove : Int -> [a] -> [a]
remove n xs = take n xs ++ drop (n+1) xs

-- TODO: use arrays in interpretation part once remove is fixed
permsE : [a] -> Enum [a]
permsE xs = let len = length xs
                choices = listE << map (\x -> takeE (len - x) smallNatE) <| [0..len - 1]
                permute is = interpret xs is []
            in permute `mapE` choices

interpret : [a] -> [Int] -> [a] -> [a]
interpret curXs curIs acc = case curIs of
  []      -> acc -- Possibly should be reverse acc, idk
  (i::is) -> let x      = head <| drop i curXs
                 newXs = remove i curXs
             in interpret newXs is (x :: acc)
