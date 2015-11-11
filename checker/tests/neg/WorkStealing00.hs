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

slave :: (DSL repr) => repr (Pid RSing -> Pid RSing -> Process repr ())
slave =  lam $ \masterPid -> lam $ \workQueuePid ->   
                do myPid <- self
                   -- ask workQueue for work
                   send workQueuePid myPid
                   (num :: repr Int)  <- recv
                   -- perform some local computation on num and send result to master
                   send masterPid num


-- wait for requests from n slaves and allot them work
workQueueProcess :: (DSL repr) => repr (Int -> Process repr ())
workQueueProcess = lam $ \n -> do doN (int 1 `plus` n) body
                                  return tt
  where body = lam $ \i -> do nextWorker <- recv
                              send nextWorker i


master :: (DSL repr) => repr (RMulti -> Int -> Process repr [Int])
master = lam $ \slaveRole  -> lam $ \n ->
               do myPid <- self
                  workQueueRole <- newRSing
                  -- start workQueue
                  workQueuePid <- spawn workQueueRole (app workQueueProcess n)
                                        
                  -- spawn the slaves
                  slaves <- spawnMany slaveRole n (app (app slave myPid) workQueuePid)
      
                  -- wait for results from slaves
                  doMany slaves (lam $ \_ -> do recv)

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 app (app master r) n
                                 ret tt


main :: IO ()
main = checkerMain (int 2 |> mainProc)



    
