{-# LANGUAGE DataKinds #-}
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

pingServer :: forall repr. (DSL repr) => repr (Int -> Process repr ())
pingServer = lam $ \n ->
  do doN "loop1" n $ lam $ \_ -> do (_ :: repr (T "Msg" ())) <- recv
                                    return tt
     return tt

master :: (DSL repr) => repr (RSing -> Int -> Process repr ())
master = lam $ \r -> lam $ \n ->
   do p <- spawn r (app pingServer n)
      doN "loop0" n (lam $ \_ -> send p (lift (TyName :: TyName "Msg") tt))
      return tt

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRSing
                                 app2 master r n

main :: IO ()
main = checkerMain (arb |> mainProc)
