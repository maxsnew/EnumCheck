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

-- | Base enumerators
natE : Enum Int
natE = { size = inf, fromNat = id }

boolE : Enum Bool
boolE = finE [True, False]

ordE : Enum Order
ordE = finE [LT, EQ, GT]
