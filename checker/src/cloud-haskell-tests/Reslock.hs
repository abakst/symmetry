{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}

module Reslock where

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

import qualified Control.Monad.State.Lazy as St

data LockM = Lock ProcessId
             deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary LockM

data AcquiredM = Acquired ProcessId
                 deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary AcquiredM

data Cmd  = Write PeanoN | Read
            deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary Cmd

data ReqM = Req ProcessId Cmd
            deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary ReqM

data UnlockM = Unlock ProcessId
               deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary UnlockM

data ResM = Ok | Reply PeanoN
              deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary ResM

data AnsM = Ans ProcessId PeanoN
            deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary AnsM

-- LOCKED RESOURCE

res_start    :: Res -> Process ProcessId
res_start res = spawnLocal (res_free res)

res_free    :: Res -> Process ()
res_free res = do (Lock p) <- expect
                  self     <- getSelfPid
                  send p (Acquired self)
                  res_locked res p

res_locked      :: Res -> ProcessId -> Process ()
res_locked res p = receiveWait [match reqHandler, match unlockHandler]
                   where reqHandler (Req p cmd) =
                           let (newres, r) = query_res res p cmd
                            in case r of
                                 Ok        -> res_locked newres p
                                 (Reply a) -> do self <- getSelfPid
                                                 send p (Ans self a)
                                                 res_locked newres p
                         unlockHandler (Unlock p) = res_free res

-- RES API

res_lock  :: ProcessId -> Process ()
res_lock q = do self <- getSelfPid
                send q (Lock self)
                let pred (Acquired q')    = q == q'
                    handler (Acquired q') = return ()
                 in receiveWait [matchIf pred handler]

res_unlock  :: ProcessId -> Process ()
res_unlock q = do self <- getSelfPid
                  send q (Unlock self)
                  return ()

res_request      :: ProcessId -> Cmd -> Process PeanoN
res_request q cmd = do self <- getSelfPid
                       send q (Req self cmd)
                       let pred (Ans q' _)    = q == q'
                           handler (Ans q' x) = return x
                        in receiveWait [matchIf pred handler]

res_do      :: ProcessId -> Cmd -> Process ()
res_do q cmd = do self <- getSelfPid
                  send q (Req self cmd)
                  return ()

-- CELL Implementation

data Res = Res PeanoN

cell_start :: Process ProcessId
cell_start  = res_start (Res Zero)

query_res                :: Res -> ProcessId -> Cmd -> (Res, ResM)
query_res (Res x) pid cmd = case cmd of
                              Write y -> (Res y, Ok)
                              Read    -> (Res x, Reply x)

cell_lock     :: ProcessId -> Process ()
cell_lock c    = res_lock c

cell_write    :: ProcessId -> PeanoN -> Process ()
cell_write c x = res_do c (Write x)

cell_read     :: ProcessId -> Process PeanoN
cell_read c    = res_request c Read

cell_unlock   :: ProcessId -> Process ()
cell_unlock c  = res_unlock c

-- INCREMENT CLIENT

inc  :: ProcessId -> Process ()
inc c = do cell_lock c
           v <- cell_read c
           cell_write c (Succ v)
           cell_unlock c
           say $ (show v) ++ " --> " ++ (show (Succ v))

reslock_main :: Process ()
reslock_main  = do c <- cell_start
                   n <- any_nat
                   say $ "going to add " ++ (show n) ++ " to 0. Simple right?"
                   add_to_cell c n
                   say $ "DONE !"

add_to_cell           :: ProcessId -> PeanoN -> Process ()
add_to_cell _ Zero     = return ()
add_to_cell c (Succ n) = spawnLocal (inc c) >> add_to_cell c n
