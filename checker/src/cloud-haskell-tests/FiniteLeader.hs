{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}

-- Description:
--
--     Three implementations of a leader election protocol
--     in an unidirectional ring of N processes.
--     Here we set N to 3 and specialise `compare` so that
--     in fact, with data abstraction Data_1, the transition system
--     is precisely captured by a finite transition system.
--     The property then can be proved by Soter.
--
--     **N.B.**: The property "Only one leader gets elected"
--     *cannot* be proven by Soter _in general_ (for N participants).
--     The correctness proof relies too heavily on
--     the choice of unique identifiers for the participants.
--     Note that this characteristic makes this problem
--     a very difficult instance for any Model Checking based
--     approach.
--
-- Reference: Adapted from Fredlund's PhD Thesis

module FiniteLeader where

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

data Elected = Elected deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary Elected
data Congratulations = Congratulations deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary Congratulations
data Out = Out ProcessId deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary Out

data MyDat = A | B | C deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary MyDat

finite_leader = testtnode >> return ()

testtnode = start (\out notary x -> tnode out notary x)
testsnode = start (\out notary x -> snode out notary x)
testdnode = start (\out notary x -> dnode out notary x)

start f = do self <- getSelfPid
             ring_abc f self
             Elected <- expect
             return Congratulations

ring_abc fun notary = do a <- spawnLocal $ do (Out out) <- expect
                                              fun out notary A
                         b <- spawnLocal (fun a notary B)
                         c <- spawnLocal (fun b notary C)
                         send a (Out c)

init_ring fun (hd:rst) notary = do pnew <- spawnLocal $ do (Out out) <- expect
                                                           fun out notary hd
                                   ring fun rst notary pnew pnew

ring fun l notary pstop pprev =
  case l of
    []     -> send pstop (Out pprev) >> return pstop
    hd:rst -> do pnew <- spawnLocal (fun pprev notary hd)
                 ring fun rst notary pstop pnew

-- first alg

data Token = Token MyDat deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary Token

tnode out notary d = send out (Token d) >> tnodeB out notary d

tnodeB out notary d = do (Token e) <- expect
                         case compare e d of
                           EQ         -> send notary Elected
                           Prelude.GT -> tnode out notary e
                           LT         -> tnodeB out notary d

snode out notary d = do send out (Token d)
                        (Token e) <- expect
                        case compare e d of
                          EQ         -> send notary Elected
                          Prelude.GT -> snode out notary e
                          LT         -> c out
c out = do v <- expect
           send out (Token v)
           c out

dnode out notary d = do send out (Token d)
                        (Token e) <- expect
                        case compare e d of
                          EQ -> send notary Elected
                          _  -> do send out (Token e)
                                   (Token f) <- expect
                                   case (compare e d, compare e f) of
                                     (Prelude.GT, Prelude.GT) -> dnode out notary e
                                     _                        -> c out
