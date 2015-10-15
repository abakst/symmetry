{-# Language RebindableSyntax #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module PingMulti00 where

import Prelude hiding ((>>=), (>>), fail, return) 
import Symmetry.Language.AST  
import Symmetry.Language.Syntax  
import Symmetry.SymbEx
import qualified Symmetry.IL.AST as IL

pingServer :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
           => repr (Process ())
pingServer = do myPid <- self
                p     <- recv
                send p myPid

master :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
       => repr (RMulti -> Int -> Process ())
master = lam $ \r -> lam $ \n ->
   do ps <- spawnMany r n pingServer
      myPid <- self
      doMany ps (lam $ \p -> send p myPid)
      doMany ps (lam $ \_ -> do (_ :: repr (Pid RSing))  <- recv
                                ret tt)
      ret tt

main :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
     => repr (Int -> ())
main = lam $ \n -> exec $ do r <- newRMulti
                             app (app master r) n

-- configs = renvs $ runSymb (main (repI 10))
