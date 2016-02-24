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

-- Signal : Either Int or () as termination signal
type SigT  = Int :+: ()

mkWork :: DSL repr => repr Int -> repr SigT
mkWork = inl

mkTerm :: DSL repr => repr SigT
mkTerm = inr tt


mapperProcess :: (DSL repr) => repr (Pid RSing -> Pid RSing -> Process repr ())
mapperProcess =  lam $ \masterPid -> lam $ \workQueuePid -> app (fixM (app (app fix_f masterPid) workQueuePid)) tt
           where fix_f = lam $ \mPid -> lam $ \wqPid -> lam $ \f -> lam $ \_->   
                       do myPid <- self
                          send wqPid myPid
                          (v :: repr SigT)  <- recv
                          match v 
                            (lam $ \val  ->  do send mPid val 
                                                app f tt)
                            (lam $ \_    -> ret tt)


workQueueProcess :: (DSL repr) => repr (Int -> Int -> Process repr ())
workQueueProcess = lam $ \n -> lam $ \k -> 
  do doN "wq0" n allotWork
     doN "wq1" k $ lam $ \_ -> do mapperPid <- recv
                                  send mapperPid mkTerm
     return tt
  where
    allotWork
      = lam $ \x -> do mapperPid <- recv
                       send mapperPid (mkWork x)


master :: (DSL repr) => repr (RMulti -> Int -> Int -> Process repr [Int])
master = lam $ \mapperRole  -> lam $ \k -> lam $ \n ->
               do myPid <- self
                  workQueueRole <- newRSing
                  workQueuePid <- spawn workQueueRole (app (app workQueueProcess n) k)
                  mappers <- spawnMany mapperRole k (app (app mapperProcess myPid) workQueuePid)
      
                  doN "l1" n (lam $ \p -> do recv)


mainProc :: (DSL repr) => repr (Int -> Int -> ())
mainProc = lam $ \k -> lam $ \n -> exec $ do r <- newRMulti
                                             app (app (app master r) k) n
                                             ret tt


main :: IO ()
main = checkerMain (app (app mainProc (int 2)) (int 3))
