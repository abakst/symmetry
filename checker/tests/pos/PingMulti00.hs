{-# Language RebindableSyntax #-}
{-# Language TypeOperators #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module PingMulti00 where

import Prelude hiding ((>>=), (>>), fail, return) 
import Symmetry.Language
import Symmetry.Verify

pingServer :: (DSL repr) => repr (Process repr ())
pingServer = do myPid <- self
                p     <- recv
                send p myPid

master :: (DSL repr) => repr (RMulti -> Int -> Process repr ())
master = lam $ \r -> lam $ \n ->
   do ps <- spawnMany r n pingServer
      myPid <- self
      doMany "l0" ps (lam $ \p -> send p myPid)
      doMany "l1" ps (lam $ \_ ->
                   do (_ :: repr (Pid RSing))  <- recv
                      return tt)
      return tt

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 app (app master r) n

main :: IO ()
main = checkerMain (arb |> mainProc)
