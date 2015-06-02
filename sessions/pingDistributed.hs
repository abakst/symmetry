module MapReduce where

import Text.Printf
import Control.Monad                    (forever)
import Control.Distributed.Process
import Control.Distributed.Process.Node
import Network.Transport.TCP            (createTransport, defaultTCPParameters)
import Bootstrap                        (execProc)

data Message = Ping ProcessId
             | Pong ProcessId
  deriving (Typeable, Generic)

instance Binary Message

{-
  G = ∀ p:pong. server -> p<Ping>; p -> server<Pong>; end
-}

{-
  T = G ↑ server
    = ∀ p:pong. !<p, Ping>; ?<p, Pong>; end
-}
master :: [NodeId] -> Process ()
master peers = do

  ps <- forM peers $ \nid -> do
          say $ printf "spawning on %s" (show nid)
          spawn nid $(mkStaticClosure 'pingServer)

  mypid <- getSelfPid

  forM_ps $ \pid -> do
    say $ printf "pinging %s" (show pid)
    send pid (Ping mypid)

  waitForPongs ps

  say "All pongs successfully received"
  terminate

waitForPongs :: [ProcessId] -> Process ()
waitForPongs [] = return ()
waitForPongs ps = do
  m <- expect
  case m of
    Pong p -> waitForPongs (filter (/= p) ps)
    _  -> say "MASTER received ping" >> terminate

{-
   T = ?<server, Ping>.!<server, Pong>
-}
pingServer :: Process ()
pingServer = do
  Ping from <- expect
  say $ printf "ping received from %s" (show from)
  mypid <- getSelfPid
  send from (Pong mypid)
