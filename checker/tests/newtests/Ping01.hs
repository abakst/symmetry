{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

client :: (DSL repr) => repr (Pid RSing -> Process repr ())
client = lam $ \master_pid -> do myPid <- self
                                 send master_pid myPid
                                 _ :: repr (Pid RSing) <- recv
                                 return tt

master :: (DSL repr) => repr
          (RSing -> Process repr ())
master = lam $ \r -> do myPid <- self
                        c     <- spawn r (app client myPid)
                        send c myPid
                        _ :: repr (Pid RSing) <- recv
                        return tt

mainProc :: (DSL repr) => repr ()
mainProc = exec $ do r <- newRSing
                     r |> master

main :: IO ()
main = checkerMain mainProc
