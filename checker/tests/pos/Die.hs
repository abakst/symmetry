{-# Language RebindableSyntax #-}
{-# Language TypeOperators    #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return) 
import Symmetry.Language
import Symmetry.Verify
import Symmetry.SymbEx

goo :: forall r. (DSL r) => r (Process r ())
goo = do x <- recv
         match (x :: r (Int :+: Int))
           (lam $ \_ -> ret tt)
           (lam $ \_ -> die )

mainProc :: forall r. (DSL r) => r (Process r ())           
mainProc = do r <- newRSing
              p <- spawn r goo
              send p (inl (int 0) :: r (Int :+: Int))

main = checkerMain (exec mainProc)
