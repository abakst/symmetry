{-# Language RebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}
module Ping00 where

import Prelude hiding ((>>=), (>>), fail, return) 
import Language.AST  
import Language.Syntax  
import SymbEx

pingServer :: SymbEx (Process ())
pingServer = do myPid <- self
                p <- recv
                send p myPid

master :: SymbEx RMulti -> SymbEx Int -> SymbEx (Process ())
master r n = do ps <- spawnMany r n pingServer
                myPid <- self
                doMany ps (lam $ \p -> send p myPid)
                doMany ps (lam $ \_ -> recv :: SymbEx (Process (Pid RSing)))
                return tt

main :: SymbEx Int -> SymbEx ()
main n = exec $ do r <- newRMulti
                   master r n
