{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
{-# Language DataKinds #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

type Ping = T "Ping" (Pid RSing)
type PPing = T "PPing" Ping

pingServer :: (DSL repr) => repr (Process repr ())
pingServer = do myPid <- self
                (p :: repr PPing) <- recv
                send (forget (forget p)) (lift (TyName :: TyName "Pong") myPid)

master :: (DSL repr) => repr
          (RSing -> Process repr ())
master = lam $ \r -> do p     <- spawn r pingServer
                        myPid <- self
                        _     <- send p (lift (TyName :: TyName "PPing") (lift (TyName :: TyName "Ping") myPid))
                        _ :: repr (T "Pong" (Pid RSing)) <- recv
                        return tt

mainProc :: (DSL repr) => repr ()
mainProc = exec $ do r <- newRSing
                     r |> master

main :: IO ()
main = checkerMain mainProc
