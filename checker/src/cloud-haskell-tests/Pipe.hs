{-# LANGUAGE ScopedTypeVariables #-}

module Pipe where

import TestMain
import Helper
import AST hiding (Process)
import Render

import Control.Distributed.Process
import Control.Distributed.Process.Serializable
import Data.Typeable.Internal
import GHC.Int

test_pipe :: IO ()
test_pipe =  mytest pipe

pipe :: Process ()
pipe =  do
  self <- getSelfPid
  n    <- getRandInRange 1 100
  head <- init_pipe (\x -> x+1) n self
  send head (0 :: Int)
  sink

init_pipe         :: (Int -> Int) -> Int -> ProcessId -> Process ProcessId
init_pipe _ 0 next = return next
init_pipe f n next = do
                       new <- spawnLocal (pipe_node f next)
                       pid <- init_pipe f (n-1) new
                       return pid

sink :: Process ()
sink = receiveWait [match (\(stat :: Int) -> say (show stat))]

pipe_node f next =
  do
    receiveWait [match handler]
  where handler (msg :: Int) = do send next (f msg)
                                  pipe_node f next

pipe_config :: Config ()
pipe_config =  Config {
  cTypes  = [],
  cSets   = [],
  cUnfold = [],
  cProcs  = []
    }
