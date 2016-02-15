{-# Language RebindableSyntax #-}
{-# Language TypeOperators #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return, not) 
import Symmetry.Language
import Symmetry.Verify

pingServer :: (DSL repr) => repr (Process repr ())
pingServer = do (_ :: repr ()) <- recv
                return tt

master :: (DSL repr) => repr (RMulti -> Int -> Process repr ())
master = lam $ \r -> lam $ \n ->
   do ps <- spawnMany r n pingServer
      -- yield (G:T, R:T)
      doMany "l0" ps body

      -- One of the invariants...
      c    <- readGhost "l0"
      assert (c `eq` n)
      assert (not (c `eq` n))

      return tt
      -- yield (G:\forall 0 <= i < n. PtrW[i] = 1; R: T)
  where
    body = lam $ \p -> do send p tt

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 app (app master r) n

main :: IO ()
main = checkerMain (arb |> mainProc)
