{-# Language RebindableSyntax #-}
{-# Language TypeOperators #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return, not, or) 
import Symmetry.Language
import Symmetry.Verify

pingServer :: forall r repr. DSL repr => repr (Pid r -> Process repr ())
pingServer = lam $ \p ->
             do ptrr  <- readPtrR (arb :: repr ())
                l0    <- readGhost p "l0"
                myIdx <- readMyIdx
                assert (not (myIdx `lt` l0) `or` (ptrr `eq` int 1))
                (_ :: repr ()) <- recv
                return tt

master :: (DSL repr) => repr (RMulti -> Int -> Process repr ())
master = lam $ \r -> lam $ \n ->
   do me <- self
      ps <- spawnMany r n (app pingServer me)
      doMany "l0" ps body

      -- One of the invariants...
      c    <- readGhost me "l0"
      -- assert (c `eq` n)
      assert (c `lt` n)

      return tt
  where
    body = lam $ \p -> do send p tt

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 app (app master r) n

main :: IO ()
main = checkerMain (arb |> mainProc)
