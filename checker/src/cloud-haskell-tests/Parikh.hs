{-# LANGUAGE ScopedTypeVariables #-}

module Parikh where

import Control.Distributed.Process
import Control.Distributed.Process.Serializable
import Data.Typeable.Internal
import GHC.Int
import Helper
import AST hiding (Process)
import Render

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
  receiveWait [
    matchMsgId2 "init" (\ (_::ProcessId)  (_::String) -> die "ERROR: We should be already initialized!"),
    matchMsgId1 "set"  (\ y -> do_serve y),
    matchMsgId1 "get"  (\ pid -> do
                            send pid x
                            do_serve x),
    matchMsg   "bye"  (die "Bye bye...")]

{- ############################# CONFIGURATION ############################# -}

parikh_config :: Config ()
parikh_config =  Config {
    cTypes  = [ init_msg_type_x
              , succ_msg_type_x
              , set_msg_type_x  ]
  , cSets   = []
  , cUnfold = []
  , cProcs  = [( pid0 {-process 0-}
               , SBlock [ SSend pid1 [(init_msg_type pid0 , SSkip ())] ()
                        , SRecv [(succ_msg_type pid0, SSkip ())] ()
                        , SSend pid1 [(set_msg_type pid0, SSkip ())] ()] ())
              ,( pid1 {-process 1-}
               , SBlock [ SRecv [ ( init_msg_type_x
                                  , SSend p_x [(succ_msg_type pid1, SSkip ())] ())] ()
                        , SLoop (LV "X")
                                (SBlock [] ()) ()] ())]
  } where pid0            = PConc 0
          pid1            = PConc 1
          pvar x          = PVar (V x)
          init_msg_type v = MTApp (MTyCon "InitType") [v]
          succ_msg_type v = MTApp (MTyCon "SuccessType") [v]
          set_msg_type v  = MTApp (MTyCon "SetType") [v]
          p_x             = pvar "x"
          init_msg_type_x = init_msg_type p_x
          succ_msg_type_x = succ_msg_type p_x
          set_msg_type_x  = set_msg_type  p_x
