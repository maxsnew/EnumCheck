module EnumCheck.Enum where

import Array
import Either (..)
import Native.Error

import EnumCheck.ExtNat (..)

type Nat = Int    
type Enum a = { size : ExtNat 
              , fromNat : Nat -> a
              }

toList : Enum a -> [a]
toList e = map e.fromNat [0 .. toInt e.size - 1]

fromNat : Nat -> Enum a -> a
fromNat n e = if | n < 0            -> Native.Error.raise "fromNat only takes nats"
                 | nat n >=! e.size -> Native.Error.raise "fromNat given index greater than size of enum"
                 | otherwise  -> e.fromNat n

-- | Combinators
finE : [a] -> Enum a
finE xs = let arr = Array.fromList xs
              len = Array.length arr
          in { size = nat len
             , fromNat = flip Array.getOrFail arr
             }

mapE : (a -> b) -> Enum a -> Enum b
mapE f e = { e | fromNat <- f . e.fromNat }

splitE : Nat -> Enum a -> (Enum a, Enum a)
splitE n e = (takeE n e, dropE n e)

takeE : Nat -> Enum a -> Enum a
takeE n es = { size = nat n
             , fromNat = es.fromNat
             }

dropE : Nat -> Enum a -> Enum a
dropE n es = { size = es.size -! nat n
             , fromNat = es.fromNat . (\x -> x + n)
             }

appendE : Enum a -> Enum a -> Enum a
appendE xs ys = { size = xs.size +! ys.size 
                , fromNat n = if nat n <! xs.size
                              then xs.fromNat n
                              else ys.fromNat (n - toInt xs.size)
                }

quotRem x y = (x `div` y, x `mod` y)

orE : Enum a -> Enum a -> Enum a
orE xs ys = 
    let newSize = xs.size +! ys.size
    in 
      if | xs.size == ys.size -> 
             { size = newSize
             , fromNat n = let (q,r) = quotRem n 2
                               e = if r == 0 then xs else ys
                           in e.fromNat q
             }
         | otherwise ->
             let (lessE, bigE, flipped) = 
                     
                     if | xs.size <=! ys.size -> (xs, ys, False)
                        | otherwise -> (ys, xs, True)
                 (belowBigE, aboveE) = splitE (toInt lessE.size) bigE
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
             let fromNat n = let flroot = floor . sqrt . toFloat <| n
                                 flrootsq = flroot * flroot
                                 diff = n - flrootsq
                                 (n1, n2) = if n - flrootsq < flroot
                                            then (diff, flroot)
                                            else (flroot, diff - flroot)
                             in (xs.fromNat n1, ys.fromNat n2)
             in { size = newS, fromNat = fromNat }
         | otherwise          ->
             let firstLess = xs.size <=! ys.size
                 lessSize = toInt <| if firstLess then xs.size else ys.size
                 fromNat n =
                     let (q, r) = quotRem n lessSize
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
         in { size = inf, fromNat n = (e ()).fromNat n }

-- | Base enumerators
natE : Enum Int
natE = { size = inf, fromNat = id }

emptyE : Enum a
emptyE = { size = nat 0, fromNat x = head [] }

boolE : Enum Bool
boolE = finE [True, False]

ordE : Enum Order
ordE = finE [LT, EQ, GT]

manyE : Enum a -> Enum [a]
manyE e = if e.size == nat 0
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
                choices = listE . map (\x -> takeE (len - x) natE) <| [0..len - 1]
                permute is = interpret xs is []
            in permute `mapE` choices

interpret : [a] -> [Int] -> [a] -> [a]
interpret curXs curIs acc = case curIs of
  []      -> acc -- Possibly should be reverse acc, idk
  (i::is) -> let x      = head <| drop i curXs
                 newXs = remove i curXs
             in interpret newXs is (x :: acc)
