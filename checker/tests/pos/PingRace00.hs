{-# Language FlexibleContexts #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeOperators #-}
{-# Language DataKinds #-}

-- {-# OPTIONS_GHC -fno-warn-unused-binds #-}
-- {-# OPTIONS_GHC -fno-warn-name-shadowing #-}
-- {-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module PingMulti02 where

import Prelude hiding ((>>=), (>>), fail, return) 
import qualified Prelude as Pre ((>>=), (>>), fail, return) 
import Symmetry.Language
import Symmetry.Verify
import SrcHelper

pingServer :: (DSL repr) => repr (Pid RSing -> Process repr ())
pingServer = lam $ \m -> do
  myPid <- self
  send m myPid
  (_ :: repr (Pid RSing)) <- recv
  return tt

master :: (DSL repr) => repr (RMulti -> Int -> Process repr ())
master = lam $ \r -> lam $ \n -> do
  myPid <- self
  ps <- spawnMany r n (myPid |> pingServer)
  doMany "l0" ps (lam $ \p -> do
                (x :: repr (Pid RSing)) <- recv
                send x myPid
                return tt)
  return tt

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do
  r <- newRMulti
  app2 master r n

main :: IO ()
main = checkerMain (arb |> mainProc)
