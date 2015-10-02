{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}

module Howait where

import TestMain
import Helper
import AST hiding (Process)
import Render

import Control.Distributed.Process
import Control.Distributed.Process.Serializable
import Data.Typeable.Internal
import GHC.Int

test_howait :: IO ()
test_howait =  mytest howait

howait :: Process ()
howait =  do peano <- getRandPInRange 0 5
             say $ "random int: " ++ (show peano)
             s <- spawnLocal serve
             l <- sp_wait1 (\x -> (client s x)) peano
             say $ "howait: " ++ (show l)

{-a server that increments the number it's given-}
serve :: Process ()
serve  = let pred (s,(_::ProcessId),(_::PeanoN)) = s == "req"
             serve_helper (_,p,x) = do
                                      self <- getSelfPid
                                      send p ("reply", self, (Succ x))
                                      serve
           in receiveWait [matchIf pred serve_helper]

{-client that sends a message to the server to increment the given number-}
client    :: ProcessId -> PeanoN -> Process PeanoN
client s n = do self <- getSelfPid
                send s ("req", self, n)
                let pred (s,(_::ProcessId),(_::PeanoN)) = s == "reply"
                    client_helper (_,_,r) = return r
                  in receiveWait [matchIf pred client_helper]

rami = do self <- getSelfPid
          send self (1 :: Int)
          send self (2 :: Int)
          send self (3 :: Int)
          i1 <- expect :: Process Int
          i2 <- expect :: Process Int
          i3 <- expect :: Process Int
          say $ (show i1) ++ " " ++ (show i2) ++ " " ++ (show i3)

{-helper function ...-}
sp_wait1             :: (PeanoN -> Process PeanoN) -> PeanoN
                     -> Process [PeanoN]
sp_wait1 f n          = sp_wait2 f (return []) n

sp_wait2             :: (PeanoN -> Process PeanoN) -> (Process [PeanoN]) -> PeanoN
                     -> Process [PeanoN]
sp_wait2 _ g Zero     = g >>= return
sp_wait2 f g (Succ n) = do self   <- getSelfPid
                           {-create a worker to calculate (n+2)-}
                           worker <- spawnLocal $ do res <- f (Succ n)     {-n + 2-}
                                                     myself <- getSelfPid
                                                     say $ (show res) ++ " " ++ (show myself)
                                                     send self ("result",myself,res)
                           let pred (s,p,(r::PeanoN)) = ((s == "result") && (p == worker))
                               g' (_,_,r)              = do l <- g
                                                            return (r : l)
                             in sp_wait2 f (receiveWait [matchIf pred g']) n

howait_config :: Config ()
howait_config =  Config {
  cTypes  = [],
  cSets   = [],
  cUnfold = [],
  cProcs  = []
  }
