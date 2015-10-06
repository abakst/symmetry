{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}

module Ring where

import TestMain
import Helper
import AST hiding (Process)
import Render

import Data.Binary
import Data.Typeable
import Data.Generics
import Control.Distributed.Process
import Control.Distributed.Process.Serializable
import Data.Typeable.Internal
import GHC.Int

test_ring :: IO ()
test_ring =  mytest ring

data MsgType = Peek PeanoN ProcessId
             | Ans [PeanoN]
             | Forward [PeanoN]
             deriving (Ord, Eq, Show, Typeable, Data)

ring :: Process ()
ring  = do xs <- getRandPLInRange 1 10 5
           p  <- init_ring slave xs
           probe_ring p

probe_ring  :: ProcessId -> Process ()
probe_ring p = do self <- getSelfPid
                  send p (Peek Zero self)
                  receiveWait [match (\(Ans _) -> say "hurray")]
                  probe_ring p

init_ring       :: (ProcessId -> PeanoN -> Process ()) -> [PeanoN] -> Process ProcessId
init_ring fun xs = spawnLocal $ bootstrap_ring2 fun xs

bootstrap_ring2       :: (ProcessId -> PeanoN -> Process ()) -> [PeanoN]
                      -> Process ()
bootstrap_ring2 fun xs = do self <- getSelfPid
                            bootstrap_ring3 fun self xs

bootstrap_ring3                :: (ProcessId -> PeanoN -> Process ()) -> ProcessId -> [PeanoN]
                               -> Process ()
bootstrap_ring3 fun prev [x]    = fun prev x
bootstrap_ring3 fun prev (x:xs) = do nxt <- spawnLocal $ fun prev x
                                     bootstrap_ring3 fun nxt xs
{-
   ("forward", x)  => nxt ! ("forward", me:x).
   ("peek",x,from) => nxt ! ("forward", me:x),
                      ("forward", y)  => from ! ("ans", y)
-}
slave       :: ProcessId -> PeanoN -> Process ()
slave nxt me = receiveWait [
                 match (\(Forward xs) -> send nxt (Forward (me:xs))),
                 match (\(Peek x from) ->
                          do send nxt (Forward [me,x])
                             receiveWait [
                               match (\(Forward ys) -> send from (Ans ys))]) ]

ring_config :: Config ()
ring_config =  Config {
  cTypes  = [],
  cSets   = [],
  cUnfold = [],
  cProcs  = []
  }


instance Binary MsgType where
  put (Peek ns pid) = put (0::Word8) >> put ns >> put pid
  put (Ans ns)      = put (1::Word8) >> put ns
  put (Forward ns)  = put (2::Word8) >> put ns
  get               = do t <- get :: Get Word8
                         case t of
                           0 -> do n <- get
                                   pid <- get
                                   return (Peek n pid)
                           1 -> do ns <- get
                                   return (Ans ns)
                           2 -> do ns <- get
                                   return (Forward ns)
