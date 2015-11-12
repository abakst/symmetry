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


type Sig  = Int :+: ()

-- send workQueue its own pid. Wait for reply from workQueue, perform work and send result to master. 
-- repeat until workQueue sends a null value.
-- fixM can take multiple arguments?
slave :: (DSL repr) => repr (Pid RSing -> Pid RSing -> Process repr ())
slave =  let fix_f = lam $ \f -> lam $ \mPid -> lam $ \wqPid ->   
                       do myPid <- self
                          -- ask workQueue for work
                          send wqPid myPid
                          (v :: repr Sig)  <- recv
                          match v 
                            (lam $ \val  ->  do send mPid val 
                                                app (app f mPid) wqPid)
                            (lam $ \_    -> ret tt)
          in lam $ \masterPid -> lam $ \workQueuePid -> do app (app (fixM fix_f) masterPid) workQueuePid
                                                           ret tt

-- Has n units of work. Wait for requests from slaves and allot them work.
-- When n units are exhausted, send any more requests the value null.
-- todo: how to represent infinite loop? 
-- this workqueue process will NOT terminate. We are only checking for termination of master and slave nodes.
workQueueProcess :: (DSL repr) => repr (Int -> Process repr ())
workQueueProcess =  let allotWork = lam $ \x -> do slavePid <- recv
                                                   send slavePid x
                    in lam $ \n -> do doN n allotWork
                                      return tt
    
                           

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
                  doN n (lam $ \p -> do recv)

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 app (app master r) n
                                 ret tt


main :: IO ()
main = checkerMain (int 10 |> mainProc)



    
