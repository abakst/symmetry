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

pingServer :: forall repr. (DSL repr) => repr (Int -> Process repr ())
pingServer = lam $ \n ->
               do doN n (lam $ \_ -> (recv :: repr (Process repr ())))
                  return tt

master :: (DSL repr) => repr (RSing -> Int -> Process repr ())
master = lam $ \r -> lam $ \n ->
   do p <- spawn r (app pingServer n)
      doN n (lam $ \_ -> send p tt)
      return tt

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRSing
                                 app (app master r) n

main :: IO ()
main = checkerMain (int 2 |> mainProc)
