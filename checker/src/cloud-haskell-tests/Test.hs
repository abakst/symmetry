{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Test where

import Helper

import Control.Distributed.Process
import Control.Distributed.Process.Serializable
import Control.Monad
import Data.Binary
import Data.Generics hiding (Generic)
import GHC.Generics
import GHC.Int

data Msg = Ping ProcessId
         | Pong
           deriving (Show, Eq, Generic, Typeable)

instance Binary Msg

expectPing = do receiveWait [matchIf pred handler]
             where pred (Ping _)     = True
                   pred _            = False
                   handler (Ping me) = return me

expectPong = do receiveWait [matchIf pred handler]
             where pred (Ping _)     = False
                   pred Pong         = True
                   handler (Ping me) = return ()

pingProc = do me <- expectPing
              send me Pong

{-
me: send(bob, Ping me)
    recv(Pong)

bob: recv(x : Msg)
     case x of
       Ping y -> send (y, Pong)

map : role -> [pid]
-}
test = do me <- getSelfPid
          p <- spawnLocal pingProc
          send p (Ping me)
          expectPong
          return ()

test2 xs = do me <- getSelfPid
              pids <- forM xs $ \_ -> spawnLocal pingProc
              forM pids $ \p -> send p (Ping me)
              forM pids $ \p -> expectPong

-- (Bob_hat) spawnMany :: Role(Bob) -> Process -> ..?
-- (Bob_hat) doMany    :: (Bob_hat) -> Process -> ..?

-- 1. rewrite 2 examples in code & IR ==> xxxMany
-- 2. tx: code -> IR

-- data Src
-- data Prc
-- tx: Src -> Prc
-- datatype (src) & dsl (2 ex) & tx (src -> proc)

data Single r = Single r
data Many r   = Many   r

{-spawn     :: r -> Process -> Single r-}
{-spawnMany :: r -> Process -> Many r-}
{-doMany    :: -}
