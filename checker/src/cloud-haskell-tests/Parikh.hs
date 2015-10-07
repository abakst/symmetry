{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}

module Parikh where

import Helper
import AST hiding (Process)
import Render
import TestMain
import ConfigParser

import Control.Distributed.Process
import Control.Distributed.Process.Serializable
import Data.Binary
import Data.Generics hiding (Generic)
import GHC.Generics
import GHC.Int

type MsgVal = String
data Msg = Init ProcessId MsgVal
         | Set MsgVal
         | Get ProcessId
         | Bye
         | OK
         deriving (Ord, Eq, Show, Typeable, Generic)

instance Binary Msg

parikh :: Process ()
parikh =  do s    <- spawnLocal server
             self <- getSelfPid
             send s (Init self "a")
             OK <- expect
             send s (Set "b")
             send s Bye

server :: Process ()
server =  do (Init pid x) <- expect
             send pid OK
             do_serve x

do_serve   :: String -> Process ()
do_serve x  = do say $ "server: serving " ++ (show x)
                 receiveWait [matchIf pred msgHandler]
              where msgHandler msg =
                      case msg of
                        (Init pid x) -> do die "ERROR: MULTIPLE!"
                        (Set y)      -> do_serve y
                        (Get pid)    -> do send pid x
                                           say $ "server: sent " ++ (show x)
                                                 ++ " to " ++ (show pid)
                                           do_serve x
                        Bye          -> do die "Bye bye..."
                        _            -> return ()
                    pred msg = case msg of
                                 OK -> False
                                 _  -> True

{- ############################# CONFIGURATION ############################# -}

parikh_config = getPoorConfig "/src/cloud-haskell-tests/Parikh.hs"

{- CONFIG START
def pid0   = (PConc 0)
def pid1   = (PConc 1)
def p_x    = (PVar (V "x"))
def p_y    = (PVar (V "y"))

def proc0 =
send pid1 {
  {InitType,pid0} => receive {
    {SuccType,pid0} => send pid0 {
      {SetType,pid0} => skip
    }
  }
}

def proc1 =
receive {
  {InitType,p_x} => send p_x {
    {SuccType,pid1} => loop X {
      receive {
        {InitType,p_y} => skip;
        {SetType,p_y}  => jump X;
        {GetType,p_y}  => send p_y {{ValType,pid1} => jump X}
      }
    }
  }
}

cTypes = [ {InitType, p_x}
         , {InitType, p_y}
         , {SetType,  p_y}
         , {GetType,  p_y} ]
cSets  = []
cProcs = [ (pid0, proc0)
         , (pid1, proc1) ]
CONFIG END -}
