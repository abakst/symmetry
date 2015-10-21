{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

pingServer :: (Symantics repr, ArbPat repr (Pid (RSing)))
           => repr (Process repr ())
pingServer = do myPid <- self
                p     <- recv
                send p myPid

master :: (Symantics repr, ArbPat repr (Pid (RSing)))
       => repr
          (RSing -> Process repr ())
master = lam $ \r -> do p     <- spawn r pingServer
                        myPid <- self
                        _     <- send p myPid
                        _ :: repr (Pid RSing) <- recv
                        return tt

mainProc :: (Symantics repr, ArbPat repr (Pid RSing))
         => repr ()
mainProc = exec $ do r <- newRSing
                     r |> master

main :: IO ()
main = checkerMain mainProc
