{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

pingServer :: (DSL repr) => repr (Process repr ())
pingServer = do myPid <- self
                -- yield G: PtrR[p] = 0
                --       R: PtrW[p] > 0
                p     <- recv
                send p myPid
                -- exit G: PtrW[p] > 0

master :: (DSL repr) => repr
          (RSing -> Process repr ())
master = lam $ \r -> do p     <- spawn r pingServer
                        myPid <- self
                        _     <- send p myPid
                        -- yield G: PtrW[p] > 0, PtrR[master] = 0
                        --       R: PtrW[master] > 0
                        _ :: repr (Pid RSing) <- recv
                        return tt
                        -- exit G: PtrR[master] = 1...

mainProc :: (DSL repr) => repr ()
mainProc = exec $ do r <- newRSing
                     r |> master

main :: IO ()
main = checkerMain mainProc
