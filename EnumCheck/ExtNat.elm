module EnumCheck.ExtNat where

import Native.Error

data ExtNat = Inf | Nat Int

inf = Inf
nat n = if n >= 0
        then Nat n
        else Native.Error.raise "Not a nat"

toInt : ExtNat -> Int
toInt (Nat n) = n

isInf n = case n of
            Inf -> True
            Nat _ -> False

(+!) : ExtNat -> ExtNat -> ExtNat
m +! n = case (m, n) of
           (Inf, _) -> m
           (_, Inf) -> n
           (Nat m, Nat n) -> Nat (m + n)

(-!) : ExtNat -> ExtNat -> ExtNat
m -! n = case (m, n) of
           (_, Inf) -> Native.Error.raise "Can't subtract infinity from a nat"
           (Inf, _) -> Inf
           (Nat m, Nat n) -> if | m <= n -> Native.Error.raise "difference is not a nat"
                                | otherwise -> Nat (m - n)

(*!) : ExtNat -> ExtNat -> ExtNat
m *! n = case (m, n) of
           (Nat 0, _) -> m
           (_, Nat 0) -> n
           (Inf, _) -> n
           (_, Inf) -> m
           (Nat m, Nat n) -> Nat (m * n)

comp : ExtNat -> ExtNat -> Order
comp m n = case (m, n) of
             (Inf, Inf) -> EQ
             (Inf, _)   -> GT
             (_, Inf)   -> LT
             (Nat m, Nat n) -> compare m n

(>=!) : ExtNat -> ExtNat -> Bool
m >=! n = comp m n /= LT

m <! n = comp m n == LT
m <=! n = comp m n /= GT