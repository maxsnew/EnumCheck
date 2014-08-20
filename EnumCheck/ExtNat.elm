module EnumCheck.ExtNat where

import BigInt as BI
import BigInt (BigInt(Zero))
import Native.Error

data ExtNat = Inf | Nat BigInt

inf = Inf

-- nat n = if n >= 0
--         then Nat n
--         else Native.Error.raise "Not a nat"

toInt : ExtNat -> BigInt
toInt (Nat n) = n

isInf n = case n of
            Inf -> True
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

(/!) : ExtNat -> Int -> ExtNat
m /! n = case m of
           Inf    -> Inf
           Nat m' -> (Nat . fst) (m' `BI.quotRem` (BI.fromInt n))

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
