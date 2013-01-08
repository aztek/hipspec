{-# LANGUAGE TemplateHaskell #-}
{-

   Compile with -fforce-recomp -fexpose-all-unfoldings -fno-ignore-interface-pragmas -fno-omit-interface-pragmas

-}
module Main where

import HipSpec.Prelude
import HipSpec
import Prelude(Bool(..), IO, undefined)
import Properties
import Definitions
import Tuples

main :: IO ()
main = hipSpec $(fileName)
    [ vars ["x", "y", "z"] (undefined :: Nat)
    , vars ["xs", "ys", "zs"] (undefined :: [Nat])
    -- Constructors
    , "[]"     `fun0` ([] :: [Nat])
    , ":"      `fun2` ((:) :: Nat -> [Nat] -> [Nat])
    -- Functions
--    , "=="     `fun2` (==)
--    , "/="     `fun2` (/=)
    , "elem"   `fun2` elem
    , "union"  `fun2` union
    , "subset" `fun2` subset
    , "++"     `fun2` ((++)   :: [Nat] -> [Nat] -> [Nat])
    ]

-- The properties needs to be mentioned here to be included
to_show = properties
