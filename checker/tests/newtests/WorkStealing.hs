{-# Language RebindableSyntax #-}
{-# Language TypeOperators #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}


module Main where

import Prelude hiding ((>>=), (>>), fail, return) 
import qualified Prelude as Pre ((>>=), (>>), fail, return) 
import Symmetry.Language
import Symmetry.Verify
import SrcHelper

-- Signal : Either Int or () as termination signal
type SigT  = Int :+: ()

mkWork :: DSL repr => repr Int -> repr SigT
mkWork = inl

mkTerm :: DSL repr => repr SigT
mkTerm = inr tt


mapperProcess :: (DSL repr) => repr (Pid RSing -> Process repr ())
mapperProcess =  lam $ \workQueuePid -> app (fixM (app fix_f workQueuePid)) tt
           where fix_f = lam $ \wqPid -> lam $ \f -> lam $ \_->   
                       do myPid <- self
                          send wqPid myPid
                          (v :: repr SigT)  <- recv
                          match v 
                            (lam $ \val  -> app f tt)
                            (lam $ \_    -> ret tt)


workQueueProcess :: (DSL repr) => repr (Int -> Pid RMulti -> Process repr ())
workQueueProcess = lam $ \n -> lam $ \ps -> 
  do doN n allotWork
     doMany ps $ lam $ \_ -> do mapperPid <- recv
                                send mapperPid mkTerm
     return tt
  where
    allotWork
      = lam $ \x -> do mapperPid <- recv
                       send mapperPid (mkWork x)

master :: (DSL repr) => repr (RMulti -> Int -> Int -> Process repr ())
master = lam $ \mapperRole  -> lam $ \k -> lam $ \n ->
               do myPid      <- self
                  masterRole <- newRSing
                  mappers    <- spawnMany mapperRole k (app mapperProcess myPid)
                  app (app workQueueProcess n) mappers


mainProc :: (DSL repr) => repr (Int -> Int -> ())
mainProc = lam $ \k -> lam $ \n -> exec $ do r <- newRMulti
                                             app (app (app master r) k) n
                                             ret tt

main :: IO ()
main =
  workerCount Pre.>>= \mapperCount ->
  jobCount Pre.>>= \workCount ->
  checkerMain $ mainProc `app` int mapperCount `app` int workCount
