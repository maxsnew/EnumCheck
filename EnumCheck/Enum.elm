module EnumCheck.Enum where

import Array
import Native.Error

import EnumCheck.ExtNat (..)

type Nat = Int    
type Enum a = { size : ExtNat 
              , fromNat : Nat -> a
              }

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
dropE n es = { size = es.size - n
             , fromNat = es.fromNat . (\x -> x + n)
             }

appendE : Enum a -> Enum a -> Enum a
appendE xs ys = { size = xs.size +! ys.size 
                , fromNat n = if nat n <! xs.size
                              then xs.fromNat n
                              else ys.fromNat (n - toInt xs.size)
                }

orE : Enum a -> Enum a -> Enum a
orE xs ys = 
    let newSize = xs.size +! ys.size
    in 
      if | xs.size == isInf ys -> 
             { size = newSize
             , fromNat n = let q = n `div` 2
                               r = n `mod` 2
                               e = if r == 0 then xs else ys
                           in e.fromNat q
             }
         | otherwise ->
             let (lessE, bigE, flipped) = 
                     if | xs.size <=! ys.size -> (xs, ys, False)
                        | otherwise -> (ys, xs, True)
                 (belowBigE, aboveE) = splitE lessE.size bigE
                 belowE = if flipped
                          then orE belowBigE lessE
                          else orE lessE belowBigE
             in appendE belowE aboveE

-- | Base enumerators
natE : Enum Int
natE = { size = inf, fromNat = id }

boolE : Enum Bool
boolE = finE [True, False]
