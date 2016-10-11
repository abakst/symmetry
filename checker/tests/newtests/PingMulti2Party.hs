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

noOfWorkers = 3

pingServer :: (DSL repr) => repr (Pid RSing -> Pid RSing -> Process repr ())
pingServer = lam $ \m -> lam $ \m2 ->
  do myPid <- self
     send m myPid
     p :: repr (Pid RSing) <- recv
     send m2 tt

master :: (DSL repr) => repr (RMulti -> Int -> Process repr ())
master = lam $ \r -> lam $ \n ->
   do r2 <- newRSing
      m2 <- spawn r2 (do doN n (lam $ \_ ->
                                   do m :: repr () <- recv
                                      return tt)
                         return tt)
      myPid <- self
      ps <- spawnMany r n (app (app pingServer myPid) m2)
      doMany ps (lam $ \p -> do p <- recv
                                send p myPid)
      return tt

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 app (app master r) n

main :: IO ()
main = checkerMain (int noOfWorkers |> mainProc)
