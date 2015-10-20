{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}

module Ring where

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

test_ring :: IO ()
test_ring =  mytest ring

data PeekM    = Peek PeanoN ProcessId
                deriving (Ord, Eq, Show, Typeable, Generic)
data AnsM     = Ans [PeanoN]
                deriving (Ord, Eq, Show, Typeable, Generic)
data ForwardM = Forward [PeanoN]
                deriving (Ord, Eq, Show, Typeable, Generic)

instance Binary PeekM
instance Binary AnsM
instance Binary ForwardM

ring  = do xs <- getRandPLInRange 1 10 5
           p  <- init_ring slave xs
           probe_ring p

probe_ring p = do self <- getSelfPid
                  send p (Peek Zero self)
                  receiveWait [match (\(Ans _) -> say "hurray")]
                  probe_ring p

init_ring fun xs = spawnLocal $ bootstrap_ring2 fun xs

bootstrap_ring2 fun xs = do self <- getSelfPid
                            bootstrap_ring3 fun self xs

bootstrap_ring3 fun prev [x]    = fun prev x
bootstrap_ring3 fun prev (x:xs) = do nxt <- spawnLocal $ fun prev x
                                     bootstrap_ring3 fun nxt xs
{-
   ("forward", x)  => nxt ! ("forward", me:x).
   ("peek",x,from) => nxt ! ("forward", me:x),
                      ("forward", y)  => from ! ("ans", y)
-}
slave nxt me = receiveWait [
                 match (\(Forward xs) -> send nxt (Forward (me:xs))),
                 match (\(Peek x from) ->
                            do send nxt (Forward [me,x])
                               receiveWait [
                                 match (\(Forward ys) -> send from (Ans ys))]) ]

ring_config =  Config {
  cTypes  = [],
  cSets   = [],
  cUnfold = [],
  cProcs  = []
  }
