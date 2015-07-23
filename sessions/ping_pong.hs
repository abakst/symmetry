module Pipe where

import Text.Printf
import Control.Monad                    (forever)  
import Control.Distributed.Process
import Control.Distributed.Process.Node
import Network.Transport.TCP            (createTransport, defaultTCPParameters)
import Bootstrap                        (execProc)
  
data Message = (Ping ProcessId | Pong ProcessId)
             
{-@  G ≐ μx.(ping --Ping--> pong . pong -- Pong --> ping . x) @-}

main :: IO ()
main = execProc $ do
         --  M me < p ▹ recv(q,<Ping q>); send(q,<Pong p>); 0 |
         --         q ▹ send(p,<Ping q>); recv(p,<Pong p>); 0 |
         --         me ▹ 0 >.
         p <- spawnLocal pongProc
         --  M me < q ▹ send(p,<Ping q>); recv(p,<Pong p>); 0 |
         --         me ▹ 0 >.
         q <- spawnLocal (pingProc p)
         -- M me < 0 >.
         return ()
           
{-
M me < λxy. me ▹ recv(me,x,<Ping y>); send(me,y,<Pong me>); end >
-}
pongProc :: Process ()
pongProc = do
  s <- getSelfPid
  Ping p <- expect
  send p (Pong s)
  pongProc

{-
pong:ProcessId -> 
M me < ∀xy. send(me,pong,<Ping me>); recv(me,x,<Pong y>)
-}
pingProc :: ProcessId -> Process ()
pingProc pong = forever $ do
  s <- getSelfPid
  send pong (Ping s)
  Pong _ <- expect


{-@ pingProc :: pong:ProcessId -> μx. send(v, pong, Ping v) . recv(v, Pong _) . x  @-}
{-@ μx. recv(v, Ping p) . send(v, p, Pong v) . x @-}
{- 
   μx. send(v, pong, Ping v) . recv(v, Pong _) . x

   ||

   μx. recv(v, Ping p)       . send(v, p, Pong v) . x 

-}
