{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}

module StateFactory where

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

data Msg1 = Msg1 ProcessId PeanoN
                 deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary Msg1

data Msg2 = Msg2 PeanoN
                 deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary Msg2

state_factory = do n1 <- any_nat
                   funWithState <- factory n1 (\_ _ -> any_nat)
                   n2 <- any_nat
                   say $ "call_loop with " ++ (show (fromPeano n2)) ++ " times"
                   call_loop n2 funWithState
                   return ()

state           :: PeanoN -> (PeanoN -> PeanoN -> Process PeanoN) -> Process a
state n newstate = do (Msg1 p input) <- expect
                      say $ "state got " ++ show (fromPeano input)
                      m <- newstate n input
                      send p (Msg2 m)
                      say $ "new state sent " ++ show (fromPeano m)
                      state m newstate

factory           :: PeanoN
                  -> (PeanoN -> PeanoN -> Process PeanoN)
                  -> Process (PeanoN -> Process PeanoN)
factory n newstate = do p  <- spawnLocal (state n newstate)
                        me <- getSelfPid
                        return $ \input ->
                          do say $ "factory sending " ++ show (fromPeano input)
                             send p (Msg1 me input)
                             (Msg2 s) <- expect
                             say $ "factory got " ++ show (fromPeano s)
                             return s

call_loop              :: PeanoN -> (PeanoN -> Process a) -> Process a
call_loop (Succ Zero) f = any_nat >>= f
call_loop (Succ n)    f = (any_nat >>= f) >> call_loop n f

any_nat :: Process PeanoN
any_nat  = getRandPInRange 1 4
