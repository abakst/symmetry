module Pipe where

import Text.Printf
import Control.Monad                    (forever)  
import Control.Distributed.Process
import Control.Distributed.Process.Node
import Network.Transport.TCP            (createTransport, defaultTCPParameters)
import Bootstrap                        (execProc)
  
data Message = (Ping ProcessId | Pong ProcessId)
             
{-@  G ≐ μx.(0 -> 1 : Ping.1 -> 0 : Pong.x) @-}
main :: IO ()
main = execProc pingPong
  where
    pingPong = do
      pong <- spawnLocal (pongProc)
      ping <- spawnLocal (pingProc pong)

{-@ μx.!<1,Ping>.?<1,Pong>.x @-}
pingProc pong = forever $ do
  s <- getSelfPid
  send pong (Ping s)
  Pong p <- expect
           
{-@ μx.?<0,Ping>.!<0,Pong>.x @-}
pongProc = forever $ do
  s <- getSelfPid
  Ping p <- expect
  send p (Pong s)
