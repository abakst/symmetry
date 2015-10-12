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

data LockM = Lock ProcessId
             deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary LockM

data AcquiredM = Acquired ProcessId
                 deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary AcquiredM

type Cmd = String
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

res_start res = spawnLocal (res_free res)

res_free res = do (Lock p) <- expect
                  self     <- getSelfPid
                  send p (Acquired self)
                  res_locked res p


res_locked res p = undefined

res :: t
    :: Pid -> Cmd-> (t,PeanoN)
-- res_locked res p = receiveWait [match reqHandler, match unlockHandler]
--                    where reqHandler (Req p cmd) =
--                            let (newres, r) = res p cmd
--                             in case r of
--                                  Ok        -> res_locked newres p
--                                  (Reply a) -> do self <- getSelfPid
--                                                  send p (Ans self a)
--                                                  res_locked newres p
--                          unlockHandler (Unlock p) = res_free res
