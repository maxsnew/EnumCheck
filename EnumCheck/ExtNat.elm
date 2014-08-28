module EnumCheck.ExtNat where

import BigInt as BI
import BigInt (BigInt(Zero))
import Native.Error

data ExtNat = Inf | Nat BigInt

inf = Inf

-- | Fails if the integer is negative
nat : BigInt -> ExtNat
nat n = if BI.gte n BI.Zero
        then Nat n
        else Native.Error.raise "Not a nat"

zero : ExtNat
zero = Nat BI.zero

toBigInt : ExtNat -> BigInt
toBigInt m = case m of
  Inf -> Native.Error.raise "Error, toBigInt: argument is Infinite"
  Nat b -> b

toInt : ExtNat -> Int
toInt = BI.toInt << toBigInt

isInf : ExtNat -> Bool
isInf n = case n of
            Inf    -> True
            Nat _ -> False

(+!) : ExtNat -> ExtNat -> ExtNat
m +! n = case (m, n) of
           (Inf, _) -> m
           (_, Inf) -> n
           (Nat m, Nat n) -> Nat (BI.add m n)

(-!) : ExtNat -> ExtNat -> ExtNat
m -! n = case (m, n) of
           (_, Inf) -> Native.Error.raise "Can't subtract infinity from a nat"
           (Inf, _) -> Inf
           (Nat m, Nat n) -> case BI.compare m n of
              GT -> Nat (m `BI.subtract` n)
              _  -> Native.Error.raise "difference is not a nat"

(*!) : ExtNat -> ExtNat -> ExtNat
m *! n = case (m, n) of
           (Nat Zero, _) -> m
           (_, Nat Zero) -> n
           (Inf, _) -> n
           (_, Inf) -> m
           (Nat m, Nat n) -> Nat (BI.multiply m n)

(/!) : ExtNat -> BigInt -> ExtNat
m /! n = case m of
           Inf    -> Inf
           Nat m' -> (Nat << fst) (m' `BI.quotRem` n)

comp : ExtNat -> ExtNat -> Order
comp m n = case (m, n) of
             (Inf, Inf) -> EQ
             (Inf, _)   -> GT
             (_, Inf)   -> LT
             (Nat m, Nat n) -> BI.compare m n

(>=!) : ExtNat -> ExtNat -> Bool
m >=! n = comp m n /= LT

m <! n = comp m n == LT
m <=! n = comp m n /= GT

min : ExtNat -> ExtNat -> ExtNat
min m n = case comp m n of
  GT -> n
  _  -> m

max : ExtNat -> ExtNat -> ExtNat
max m n = case comp m n of
  LT -> n
  _  -> m
