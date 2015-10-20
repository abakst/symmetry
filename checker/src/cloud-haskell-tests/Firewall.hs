{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}

module Firewall where

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

type FWO = Either PeanoN String

test_firewall :: IO ()
test_firewall =  mytest firewall

firewall :: Process ()
firewall  = getRandPLInRange 0 10 5 >>= start

start  :: [PeanoN] -> Process ()
start l = do srv <- spawnLocal $ server Firewall.pred
             fir <- spawnLocal $ server $ fw srv notZero
             sendall fir l

sendall          :: ProcessId -> [PeanoN] -> Process ()
sendall to []     = return ()
sendall to (x:xs) = do self <- getSelfPid
                       say $ "calling " ++ (show $ fromPeano  x)
                       send to ("call", self, x)
                       (msg,pid,res) <- expect :: Process (String, ProcessId, (Either PeanoN String))
                       let res_str = case res of
                                       Left p  -> (show $ fromPeano x) ++ "-1=" ++ (show $ fromPeano p)
                                       Right s -> s
                         in do say res_str
                               sendall to xs

pred         :: PeanoN -> Process FWO
pred Zero     = die "Zero doesn't have a successor"
pred (Succ n) = return (Left n)

notZero Zero     = False
notZero (Succ _) = True

server            :: (PeanoN -> Process FWO) -> Process ()
server handle_call = do self <- getSelfPid
                        let pred (s,(_::ProcessId),_) = s == "call"
                            handler (_,from,par) =
                              do res <- handle_call par
                                 send from ("answer", self, res)
                          in do receiveWait [matchIf pred handler]
                                server handle_call

fw       :: ProcessId -> (PeanoN -> Bool) -> PeanoN -> Process FWO
fw pr t x = case t x of
              True  -> do self <- getSelfPid
                          send pr ("call", self, x)
                          let pred (s,pr',_) = (s == "answer") && (pr' == pr)
                              handler (_,(pr'::ProcessId),(res::FWO)) = return res
                            in receiveWait [matchIf pred handler]
              False -> return (Right "DON'T GIVE ME ZERO !!!")


firewall_config :: Config ()
firewall_config =  Config {
  cTypes  = [],
  cSets   = [],
  cUnfold = [],
  cProcs  = []
  }
