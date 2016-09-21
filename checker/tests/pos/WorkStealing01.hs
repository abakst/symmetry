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

-- send workQueue its own pid. Wait for reply from workQueue, perform work and send result to master. 
-- repeat until workQueue sends a null value.
slave :: (DSL repr) => repr (Pid RSing -> Pid RSing -> Process repr ())
slave =  lam $ \masterPid -> lam $ \workQueuePid -> app (fixM (app (app fix_f masterPid) workQueuePid)) tt
           where fix_f = lam $ \mPid -> lam $ \wqPid -> lam $ \f -> lam $ \_->   
                       do myPid <- self
                          -- ask workQueue for work
                          send wqPid myPid
                          (v :: repr SigT)  <- recv
                          match v 
                            -- if receive work, send result to master and repeat again.
                            (lam $ \val  ->  do send mPid val 
                                                app f tt)
                            -- if receive null, terminate.
                            (lam $ \_    -> ret tt)




-- Has n units of work. Wait for requests from slaves and allot them work.
-- When n units are exhausted, send any more requests from slaves the value null.
-- todo: add infinite loop. type errors
-- this workqueue process will NOT terminate. We are only checking for termination of master and slave nodes.

workQueueProcess :: forall repr.
                    DSL repr
                 => repr (Int -> Process repr ())
workQueueProcess =   
                     lam $ \n -> do doN "l1" n allotWork
                                    -- app (fixM fix_loopInf) tt

                                    -- Deadlocks:
                                    forever $ do slavePid <- recv
                                                 send slavePid mkTerm
                       
                       where
                         allotWork :: repr (Int -> Process repr ())
                         allotWork = lam $ \x -> do slavePid <- recv
                                                    send slavePid (mkWork x)
                             {-fix_loopInf = lam $ \f -> lam $ \_ -> do (slavePid :: repr (Pid RSing)) <- recv
                                                                      send slavePid (inr tt)
                                                                      app f tt-}

                           

-- two different parameters : number of slaves = k, number of work units = n
-- start k slaves. start workQueue with parameter. Wait for n results from the slaves.
master :: (DSL repr) => repr (RMulti -> Int -> Int -> Process repr [Int])
master = lam $ \slaveRole  -> lam $ \k -> lam $ \n ->
               do myPid <- self
                  workQueueRole <- newRSing

                  -- start workQueue with total work units = n
                  workQueuePid <- spawn workQueueRole (app workQueueProcess n)
                                        
                  -- spawn k slaves
                  slaves <- spawnMany slaveRole k (app (app slave myPid) workQueuePid)
      
                  -- wait for n results.
                  doN "l0" n (lam $ \p -> do recv)


mainProc :: (DSL repr) => repr (Int -> Int -> ())
mainProc = lam $ \k -> lam $ \n -> exec $ do r <- newRMulti
                                             app (app (app master r) k) n
                                             ret tt


main :: IO ()
main = checkerMain (app (app mainProc arb) arb)



    
