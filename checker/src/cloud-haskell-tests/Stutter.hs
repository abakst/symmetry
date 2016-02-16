{-# LANGUAGE ScopedTypeVariables #-}

module Stutter where

import TestMain
import Helper
import AST hiding (Process)
import Render

import Control.Distributed.Process
import Control.Distributed.Process.Serializable
import Data.Typeable.Internal
import GHC.Int

test_stutter :: IO ()
test_stutter =  mytest stutter

stutter :: Process ()
stutter =  do p <- spawnLocal (sttr (\(b :: Bool) -> dosmt b))
              sendF p
              wait 2

dosmt      :: Bool -> Process ()
dosmt False = die "We don't want a False"
dosmt True  = say "We love True"

sendF :: ProcessId -> Process ()
sendF p = do send p False
             sendT p

sendT :: ProcessId -> Process ()
sendT p = do send p True
             sendF p

sttr  :: (Bool -> Process ()) -> Process ()
sttr f = do expect :: Process Bool
            unsttr f

unsttr  :: (Bool -> Process ()) -> Process ()
unsttr f = do b <- expect
              f b
              sttr f

stutter_config :: Config ()
stutter_config =  Config {
  cTypes  = [],
  cSets   = [],
  cUnfold = [],
  cProcs  = [(pid0, Loop (LV "X")
                          (Send pid1 [(msg_t0
                                       ,Send pid1 [(msg_t0
                                                    ,Goto (LV "X") ())] () )] ()) ())
            ,(pid1, Loop (LV "Y")
                          (Recv [(msg_t1
                                  ,Recv [(msg_t1
                                          ,NonDet [Skip () {-failure case ?-}
                                                   ,Goto (LV "Y") ()])] ())] ()) ())]
  } where pid0    = PConc 0
          pid1    = PConc 1
          msg_t v = MTApp (MTyCon "msg") [v]
          msg_t0  = msg_t pid0
          msg_t1  = msg_t pid1
