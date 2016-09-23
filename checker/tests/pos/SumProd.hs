{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
{-# Language TypeOperators #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

type Msg = (Int, ()) :+: (Int, Pid RSing)  

pingServer :: (DSL repr) => repr (Process repr ())
pingServer = do myPid <- self
                p :: repr Msg <- recv
                match p
                   (lam $ \m -> return tt)
                   (lam $ \m -> send (proj2 m) tt)

master :: forall repr.
          (DSL repr) => repr
          (RSing -> Process repr ())
master = lam $ \r -> do p     <- spawn r pingServer
                        myPid <- self
                        _     <- send p (inr (pair (int 0) myPid) :: repr Msg)
                        _ :: repr () <- recv
                        return tt

mainProc :: (DSL repr) => repr ()
mainProc = exec $ do r <- newRSing
                     r |> master

main :: IO ()
main = checkerMain mainProc
