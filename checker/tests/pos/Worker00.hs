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

continue :: DSL repr => repr (() :+: ())  
continue = inl tt 
           
stop :: DSL repr => repr (() :+: ())  
stop = inr tt 

main :: IO ()
main = checkerMain $ (arb |> mainProc)

mainProc :: forall repr. (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRSing
                                 p <- spawn r workerProc
                                 let x = arb :: repr (() :+: ())
                                 match x (lam $ \_ -> send p continue)
                                         (lam $ \_ -> return tt)
                                 send p stop
       
workerProc :: forall repr. (DSL repr) => repr (Process repr ())
workerProc = app (fixM loop) tt
  where
    loop = lam $ \next -> lam $ \_ ->
             do (m :: repr (() :+: ())) <- recv
                match m (lam $ \_ -> app next tt)
                        (lam $ \_ -> return tt)
