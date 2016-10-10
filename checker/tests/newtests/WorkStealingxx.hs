{-# LANGUAGE DataKinds #-}
{-# Language RebindableSyntax #-}
{-# Language TypeOperators #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}


module Main where

import Prelude hiding ((>>=), (>>), fail, return) 
import Symmetry.Language
import Symmetry.Verify
import SrcHelper

type HW  = T "HasWork" Boolean
liftHW :: (DSL repr) => repr Boolean -> repr HW
liftHW =  lift (TyName :: TyName "HasWork")

type MP = T "MasterPid" (Pid RSing)
liftMP :: (DSL repr) => repr (Pid RSing) -> repr MP
liftMP =  lift (TyName :: TyName "MasterPid")

type WP = T "WorkerPid" (Pid RSing)
liftWP :: (DSL repr) => repr (Pid RSing) -> repr WP
liftWP =  lift (TyName :: TyName "WorkerPid")

workerProcess :: (DSL repr) => repr (Pid RSing -> Process repr ())
workerProcess = lam $ \masterPid ->
  let -- fix_f :: repr ((() -> Process repr ()) -> () -> Process repr ())
      fix_f = lam $ \f -> lam $ \_ ->
                do myPid <- self
                   send masterPid (liftWP myPid)
                   (hw :: repr HW) <- recv
                   match (forget hw)
                     (lam $ \_ -> app f tt)
                     (lam $ \_ -> ret tt)
  in do app (fixM fix_f) tt
        ret tt

workQueueProcess :: (DSL repr) => repr (Int -> Pid RMulti -> Process repr ())
workQueueProcess = lam $ \k -> lam $ \ps -> 
  do doN "wq0" k $ lam $ \x ->
       do (workerPid :: repr WP) <- recv
          send (forget workerPid) (liftHW (inl tt)) -- send true
     doMany "wq1" ps $ lam $ \_ ->
       do (workerPid :: repr WP) <- recv
          send (forget workerPid) (liftHW (inr tt)) -- send false
     return tt

master :: (DSL repr) => repr (Int -> Int -> Process repr ())
master = lam $ \n -> -- worker count
         lam $ \k -> -- job count
  do workerR   <- newRMulti -- workers
     masterPid <- self
     workers   <- spawnMany workerR n (app workerProcess masterPid)
     app2 workQueueProcess k workers
     ret tt


main :: IO ()
main = checkerMain $ exec (app2 master arb arb)
