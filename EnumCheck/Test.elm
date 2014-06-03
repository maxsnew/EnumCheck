module EnumCheck.Test where

import Either (..)

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

runTest : Test a -> Int -> Either Error Pass
runTest t suggNum =
    let numTests = case t.src.size of
                     Inf -> suggNum
                     Nat n -> min n (toInt t.src.size)
        loop cur = if cur >= numTests
                   then Right (show numTests ++ " tests passed.")
                   else case t.run (fromNat cur t.src) of
                          Nothing  -> loop (cur + 1)
                          Just err -> Left (show cur ++ " tests passed. " ++ "Test " ++ show (cur + 1) ++ " failed: " ++ err)
    in loop 0