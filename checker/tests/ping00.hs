{-# Language RebindableSyntax #-}
module Ping00 where

import Prelude (($)) 
import Language.AST  
import Language.Syntax  
import SymbEx

pingServer :: SymbEx (Process ())
pingServer = do myPid <- self
                p <- recv
                send p myPid

master :: SymbEx RSing -> SymbEx (Process ())
master r = do p <- spawn r pingServer
              myPid <- self
              _ <- send p myPid
              _ <- recv :: SymbEx (Process (Pid RSing))
              return tt

main :: SymbEx ()
main = exec $ do r <- newRSing
                 master r
