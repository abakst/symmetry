{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
module Ping00 where

import Prelude hiding ((>>=), (>>), fail, return)
import Language.AST
import Language.Syntax
import SymbEx

pingServer :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
           => repr (Process ())
pingServer = do myPid <- self
                p     <- recv
                send p myPid

master :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
       => repr RSing
       -> repr (Process ())
master r = do p     <- spawn r pingServer
              myPid <- self
              _     <- send p myPid
              _ :: repr (Pid RSing) <- recv
              return tt

main :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
     => repr ()
main = exec $ do r <- newRSing
                 master r

res :: SymbState
res = runSymb main
