module Main where

import BigInt as I
import EnumCheck.Enum as E
import IO.IO (..)

natStrings = I.toString `E.mapE` E.natE

-- About 10 seconds
console = putStrLn << show <| E.fromNat (I.fromString "531111") (E.pairE natStrings natStrings)
