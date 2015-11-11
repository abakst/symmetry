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

recvUnit :: forall repr. (DSL repr) => repr (Process repr ())
recvUnit = recv

pingServer :: forall repr. (DSL repr) => repr (Int -> Pid RSing -> Process repr ())
pingServer = lam $ \n -> lam $ \p ->
               do doN n (lam $ const (recvUnit >> send p tt))
                  return tt

master :: forall repr. (DSL repr) => repr (RSing -> Int -> Process repr ())
master = lam $ \r -> lam $ \n ->
   do me <- self
      p <- spawn r (app (app pingServer n) me)
      doN n (lam $ const (send p tt >> recvUnit))
      return tt

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRSing
                                 app (app master r) n

main :: IO ()
main = checkerMain (arb |> mainProc)
