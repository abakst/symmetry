{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
module Ping00 where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import Symmetry.IL.Render
import Symmetry.SymbEx

pingServer :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
           => repr (Process ())
pingServer = do myPid <- self
                p     <- recv
                send p myPid

master :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
       => repr
          (RSing -> Process ())
master = lam $ \r -> do p     <- spawn r pingServer
                        myPid <- self
                        _     <- send p myPid
                        _ :: repr (Pid RSing) <- recv
                        return tt

main :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
     => repr ()
main = exec $ do r <- newRSing
                 app master r

-- res :: SymbState
res = render . rEnvToConfig . head . renvs $ runSymb main
