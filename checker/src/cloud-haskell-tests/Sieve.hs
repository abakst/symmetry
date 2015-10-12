{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}

module Sieve where

import Prelude hiding (lookup, read)
import TestMain
import Helper
import AST hiding (Process)
import Render

import Control.Distributed.Process
import Control.Distributed.Process.Serializable

import Data.Binary
import Data.Generics hiding (Generic)
import GHC.Generics
import GHC.Int

data PokeM = Poke ProcessId
             deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary PokeM

data AnsM = Ans Int
             deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary AnsM

sieve_main = do me <- getSelfPid
                gen <- spawnLocal (counter 2)
                spawnLocal (sieve gen me)
                dump

dump = do x <- expect :: Process Int
          say (show x)
          dump

counter n = do (Poke from) <- expect
               send from (Ans n)
               counter (n+1)

sieve input output = do self <- getSelfPid
                        send input (Poke self)
                        (Ans x) <- expect
                        send output x
                        f <- spawnLocal (filter2 (divisible_by x) input)
                        sieve f output

filter2 test input = do (Poke from) <- expect
                        filter3 test input from

filter3 test input output = do self <- getSelfPid
                               send input (Poke self)
                               (Ans y) <- expect
                               case test y of
                                 False -> send output (Ans y) >> filter2 test input
                                 True  -> filter3 test input output

divisible_by x y = case y `mod` x of
                     0 -> True
                     _ -> False
