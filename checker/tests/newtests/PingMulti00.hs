{-# LANGUAGE DataKinds #-}
{-# Language RebindableSyntax #-}
{-# Language TypeOperators #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module PingMulti00 where

import Prelude hiding ((>>=), (>>), fail, return) 
import qualified Prelude as Pre ((>>=), (>>), fail, return) 
import Symmetry.Language
import Symmetry.Verify
import SrcHelper

pongServer :: (DSL repr) => repr (Process repr ())
pongServer = do myPid <- self
                (p :: repr (Pid RSing)) <- recv
                send p myPid

master :: (DSL repr) => repr (RMulti -> Int -> Process repr ())
master = lam $ \r -> lam $ \n ->
   do ps <- spawnMany r n pongServer
      myPid <- self
      doMany ps (lam $ \p -> send p myPid)
      doMany ps (lam $ \_ ->
                    do (_ :: repr (Pid RSing))  <- recv
                       return tt)
      return tt

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 app2 master r n

main :: IO ()
main =
  workerCount Pre.>>= \noOfWorkers ->
  checkerMain (int noOfWorkers |> mainProc)
