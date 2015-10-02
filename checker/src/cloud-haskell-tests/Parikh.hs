{-# LANGUAGE ScopedTypeVariables #-}

module Parikh where

import Helper
import AST hiding (Process)
import Render
import TestMain

import Control.Distributed.Process
import Control.Distributed.Process.Serializable
import Data.Typeable.Internal
import GHC.Int

parikh :: Process ()
parikh =  do
  s    <- spawnLocal server
  self <- getSelfPid
  send s ("init", self, "a")
  waitForSuccess
  send s ("set", "b")
  send s "bye"

server :: Process()
server = do
  receiveWait [matchMsgId2 "init" initHandler]
  where initHandler pid x = do
                              sendSuccess pid
                              do_serve x

do_serve   :: String -> Process()
do_serve x = do
  say x
  receiveWait [matchMsgId2 "init" (\ (_::ProcessId)  (_::String) -> die "ERROR: We should be already initialized!")
              ,matchMsgId1 "set"  (\ y -> do_serve y)
              ,matchMsgId1 "get"  (\ pid -> do
                                              send pid x
                                              do_serve x)
              ,matchMsg   "bye"  (die "Bye bye...")]

{- ############################# CONFIGURATION ############################# -}

parikh_config :: Config ()
parikh_config =  Config {
    cTypes  = [init_msg_type p_x
              ,init_msg_type p_y
              ,set_msg_type p_y
              ,get_msg_type p_y]
  , cSets   = []
  , cUnfold = []
  , cProcs  = [(pid0 {-process 0-},
                SSend pid1 [(init_msg_type pid0,
                  SRecv [(succ_msg_type pid0,
                    SSend pid1 [(set_msg_type pid0, 
                      SSkip ())] ())] ())] ())
              ,(pid1 {-process 1-},
                SRecv [(init_msg_type p_x,
                  SSend p_x [(succ_msg_type pid1,
                    SLoop (LV "X")
                      (SRecv [(init_msg_type p_y, SSkip () {-die?-})
                             ,(set_msg_type p_y ,SVar (LV "X") ())
                             ,(get_msg_type p_y ,SSend p_y [(val_msg_type pid1, SVar (LV "X") ())] () )]  () ) ())] () )] ())]
  } where pid0            = PConc 0
          pid1            = PConc 1
          pvar x          = PVar (V x)
          p_x             = pvar "x"
          p_y             = pvar "y"
          init_msg_type v = MTApp (MTyCon "InitType") [v]
          succ_msg_type v = MTApp (MTyCon "SuccessType") [v]
          set_msg_type v  = MTApp (MTyCon "SetType") [v]
          get_msg_type v  = MTApp (MTyCon "GetType") [v]
          val_msg_type v  = MTApp (MTyCon "ValType") [v]
