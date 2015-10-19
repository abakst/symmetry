{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

pingServer :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
           => repr
              (Process ())
pingServer = do myPid <- self
                p     <- recv
                send p myPid

master :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
       => repr
          (RSing -> Process ())
master = lam $ \r -> do p     <- spawn r pingServer
                        myPid <- self
                        _ :: repr (Pid RSing) <- recv
                        return tt

mainProc :: (Symantics repr, SymSend repr (Pid RSing), SymRecv repr (Pid RSing))
         => repr ()
mainProc = exec $ do r <- newRSing
                     r |> master

main :: IO ()
main = checkerMain mainProc
