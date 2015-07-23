{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, DeriveGeneric #-}
{-# OPTIONS_GHC -Wall #-}
import Control.Distributed.Process hiding (Message)
import Control.Distributed.Process.Closure

import Control.Monad
import Text.Printf
import GHC.Generics (Generic)
import Data.Binary
import Data.Typeable

import DistribUtils

-- <<Message
data Message = Ping ProcessId
             | Pong ProcessId
  deriving (Typeable, Generic)          -- <1>

instance Binary Message                 -- <2>
-- >>

-- <<pingServer
{-
pingServer :: P me < me ▹ ∀p. recv(Ping p); send p (Pong me) > () 
-}
pingServer :: Process ()
pingServer = do
  Ping from <- expect                              -- <1>
  say $ printf "ping received from %s" (show from) -- <2>
  mypid <- getSelfPid                              -- <3>
  send from (Pong mypid)                           -- <4>
-- >>

-- <<remotable
remotable ['pingServer]
-- >>

-- <<master
{-
G = foreach (p ∈ p[]):
      me --> p <Ping me>; 
    foreach (p ∈ p[]):
      p --> me <Pong p>;

G ↑ p ∈ p[] = recv(Ping me); send(me, Pong p);
G ↑ me      = foreach (p ∈ p[]): 
                send(p, Ping me);
              foreach (p ∈ p[]):
                recv(p, Pong p);
-}

{-
master :: P me < p[n] ▹ ∃q. recv(Ping q); send q (Pong q);
                 me   ▹ foreach(pi ∈ p[n]):
                          send(pi, Ping me) 
                        foreach(pi ∈ p[n]):
                          recv(Pong _)
               > () 
-}
master :: [NodeId] -> Process ()                     -- <1>
master peers = do

  ps <- forM peers $ \nid -> do                      -- <2>
          say $ printf "spawning on %s" (show nid)
          spawn nid $(mkStaticClosure 'pingServer)

  mypid <- getSelfPid

  forM_ ps $ \pid -> do                              -- <3>
    say $ printf "pinging %s" (show pid)
    send pid (Ping mypid)

  waitForPongs ps                                    -- <4>

  say "All pongs successfully received"
  terminate
  
waitForPongs :: [ProcessId] -> Process ()            -- <5>
waitForPongs [] = return ()
waitForPongs ps = do
  m <- expect
  case m of
    Pong p -> waitForPongs (filter (/= p) ps)
    -- _  -> say "MASTER received ping" >> terminate

waitForPongs' :: [ProcessId] -> Process ()
waitForPongs' = 
  forM_ ps $ const $ do { Pong _ <- expect; return () }

-- >>

-- <<main
main :: IO ()
main = distribMain master Main.__remoteTable
-- >>
