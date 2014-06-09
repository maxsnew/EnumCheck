module EnumCheck.Test where

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
    let numTests = case t.src.size of
                     Inf -> suggNum
                     Nat n -> min n (toInt t.src.size)
        loop cur fuel =
            if | fuel > 1000      -> T.Continue (\_ -> loop cur 0)
               | cur >= numTests -> T.Done . Right <| show numTests ++ " tests passed."
               | otherwise       ->
                   case t.run (fromNat cur t.src) of
                     Nothing  -> loop (cur + 1) (fuel + 1)
                     Just err ->
                         let msg = show cur ++ " tests passed. " ++ "Test " ++ show (cur + 1) ++ " failed: " ++ err
                         in T.Done . Left <| msg
    in T.trampoline <| loop 0 0
