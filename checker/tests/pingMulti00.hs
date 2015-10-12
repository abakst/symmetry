{-# Language RebindableSyntax #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}
module PingMulti00 where

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
       => repr RMulti
       -> repr Int
       -> repr (Process ())
master r n = do ps    <- spawnMany r n pingServer
                myPid <- self
                doMany ps (lam $ \p -> send p myPid)
                doMany ps (lam $ \_ -> do (_ :: repr (Pid RSing))  <- recv
                                          ret tt)
                ret tt

main :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
     => repr Int
     -> repr ()
main n = exec $ do r <- newRMulti
                   master r n

res = renv $ runSymb (main (repI 10))
