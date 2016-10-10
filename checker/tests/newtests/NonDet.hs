{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
{-# Language DataKinds #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify
import Data.Either

pingServer :: (DSL repr) => repr (Process repr ())
pingServer = do myPid <- self
                (p :: repr (T "Msg" (Int :+: Int)) ) <- recv
                return tt

master :: (DSL repr) => repr
          (RSing -> Process repr ())
master = lam $ \r -> do p     <- spawn r pingServer
                        myPid <- self
                        msg   <- nondetVal (lift (TyName :: TyName "Msg") (inl (int 0)))
                                           (lift (TyName :: TyName "Msg") (inr (int 1)))
                        _     <- send p msg
                        return tt

mainProc :: (DSL repr) => repr ()
mainProc = exec $ do r <- newRSing
                     r |> master

main :: IO ()
main = checkerMain mainProc
