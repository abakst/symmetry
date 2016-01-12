{-# Language RebindableSyntax #-}
{-# Language TypeOperators    #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return) 
import Symmetry.Language
import Symmetry.Verify

goo :: forall dsl.
       DSL dsl => dsl (Pid RSing -> Process dsl ())
goo = lam $ \p -> 
      do x <- recv
         match (x :: dsl (Int :+: Int))
           (lam $ \a -> send p a)
           (lam $ \b -> send p b)

boo :: forall dsl.
       DSL dsl => dsl (Pid RSing -> Process dsl ())
boo = lam $ \p -> do
         send p (inl (int 0) :: dsl (Int :+: Int))
         recv :: dsl (Process dsl Int)
         return tt

main :: IO ()
main = checkerMain (exec $ do r <- newRSing
                              m <- self
                              p <- spawn r (app goo m)
                              app boo p)
