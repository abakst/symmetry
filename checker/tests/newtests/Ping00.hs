{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
{-# Language DataKinds #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

pongServer :: (DSL repr) => repr (Process repr ())
pongServer = do myPid <- self
                (p :: repr (Pid RSing)) <- recv
                send p myPid

master :: (DSL repr) => repr
          (RSing -> Process repr ())
master = lam $ \r -> do p     <- spawn r pongServer
                        myPid <- self
                        send p myPid
                        (_ :: repr (Pid RSing)) <- recv
                        return tt

mainProc :: (DSL repr) => repr ()
mainProc = exec $ do r <- newRSing
                     r |> master

main :: IO ()
main = checkerMain mainProc
