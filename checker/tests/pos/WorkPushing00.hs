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


--factorial :: Int -> Int
--factorial n = foldl (*) 1 [1..n]

slave :: (DSL repr) => repr (Pid RSing -> Process repr ())
slave =  lam $ \pid ->  
                do (num :: repr Int)  <- recv
                   -- perform some local computation on num
                   send pid num

-- | Wait for n integers and sum them all up
{- 
sumIntegers :: (DSL repr) => repr (Int -> Process repr Int)
sumIntegers = app go 0
  where
    go :: repr (Int -> Int -> Process repr Int)
    go  = lam $ \acc -> lam $ \n -> 
       match (app go acc)
       (lam $ \0 -> ret (int acc))
       (lam $ \n -> do m <- recv
                       app (app go (acc + m)) (n - 1)) 
-}     

master :: (DSL repr) => repr (RMulti -> Int -> Process repr [Int])
master = lam $ \r -> lam $ \n ->
   do myPid <- self
      ps <- spawnMany r n (app slave myPid)      
      doMany "l0" ps (lam $ \p -> send p (int 4))
      doMany "l1" ps (lam $ \p -> do recv)
    
      --app sumIntegers n

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 app (app master r) n
                                 ret tt

main :: IO ()
main = checkerMain (int 2 |> mainProc)

