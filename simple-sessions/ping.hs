{-# Language TypeOperators #-}
module Main where

import Control.Concurrent.SimpleSession.Positional
import Control.Concurrent.SimpleSession.SessionTypes
import Control.Monad.Indexed

data Message = Ping | Pong
             
m1 >>> m2 = m1 >>>= \_ -> m2
  
-- | Send a ping message over a channel, then wait for pong
pingSession c = enter c >>> loop
  where loop = 
          send c Ping >>> recv c >>> zero c >>> loop
         
pongSession c = enter c >>> loop
  where loop =
          recv c >>> send c Pong >>> zero c >>> loop

main :: IO ()
main = runSession $
  io newRendezvous >>>= \r ->
    (forkSession $ accept r pingSession) >>>= \_ ->
    request r pingSession
