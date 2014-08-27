module EnumCheck.Test where

import BigInt as BI
import Either (..)
import Trampoline as T

import EnumCheck.Enum (..)
import EnumCheck.ExtNat (..)

maxInt = 2 ^ 53
type Error = String
type Pass  = String

type Test a = { run : a -> Maybe Error
              , src : Enum a
              }

expectEq a b = if a == b
               then Nothing
               else Just ("Expected " ++ show a ++ " but got " ++ show b)

runTest : Int -> Test a -> Either Error Pass
runTest suggNum t =
    let bigSugg = BI.fromInt suggNum
        numTests = case t.src.size of
                     Inf -> bigSugg
                     Nat n -> BI.min n bigSugg
        loop : BI.BigInt -> Int -> T.Trampoline (Either Error Pass)
        loop cur fuel =
            if | fuel > 1000      -> T.Continue (\_ -> loop cur 0)
               | BI.gte cur numTests -> T.Done << Right <| (BI.toString numTests) ++ " tests passed."
               | otherwise       ->
                   case t.run (fromNat cur t.src) of
                     Nothing  -> loop (BI.inc cur) (fuel + 1)
                     Just err ->
                         let msg = BI.toString cur ++ " tests passed. " ++ "Test " ++ BI.toString (BI.inc cur) ++ " failed: " ++ err
                         in T.Done << Left <| msg
    in T.trampoline <| loop BI.zero 0
