{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

pingServer :: (DSL repr) => repr (Process repr ())
pingServer = do myPid <- self
                forever (loop myPid) tt
  where
    loop me = lam $ \_ -> do
                p     <- recv
                send p me

master :: (DSL repr) => repr
          (RSing -> Process repr ())
master = lam $ \r -> do p     <- spawn r pingServer
                        myPid <- self
                        _     <- send p myPid
                        _ :: repr (Pid RSing) <- recv
                        return tt

mainProc :: (DSL repr) => repr ()
mainProc = exec $ do r <- newRSing
                     r |> master

main :: IO ()
main = checkerMain mainProc
