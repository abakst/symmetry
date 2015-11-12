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


-- 
slave :: (DSL repr) => repr (Pid RSing -> Pid RSing -> Process repr ())
slave =  lam $ \masterPid -> lam $ \workQueuePid ->   
                do myPid <- self
                   -- ask workQueue for work
                   send workQueuePid myPid
                   (num :: repr Int)  <- recv
                   -- perform some local computation on num and send result to master
                   send masterPid num


-- Has n units of work. Wait for requests from slaves and allot them work.
-- todo: When n units are exhausted, send any more requests the value null.
workQueueProcess :: (DSL repr) => repr (Int -> Process repr ())
workQueueProcess =  let allotWork x = do slavePid <- recv
                                         send slavePid x
                    in lam $ \n ->
                           do doN n (lam $ \x -> allotWork x)
                              return tt
                           


master :: (DSL repr) => repr (RMulti -> Int -> Process repr [Int])
master = lam $ \slaveRole  -> lam $ \n ->
               do myPid <- self
                  workQueueRole <- newRSing
                  -- start workQueue
                  workQueuePid <- spawn workQueueRole (app workQueueProcess n)
                                        
                  -- spawn the slaves
                  slaves <- spawnMany slaveRole n (app (app slave myPid) workQueuePid)
      
                  -- wait for results from slaves
                  doMany slaves (lam $ \p -> do recv)

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 app (app master r) n
                                 ret tt


main :: IO ()
main = checkerMain (int 10 |> mainProc)



    
