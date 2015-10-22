{-# Language RebindableSyntax #-}
{-# Language TypeOperators    #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}
module Types00 where

import Prelude hiding ((>>=), (>>), fail, return) 
import Symmetry.Language
import Symmetry.Verify

goo :: forall dsl.
       DSL dsl => dsl (Process dsl ())
goo = do x <- recv
         match (x :: dsl (Int :+: Int))
           (lam $ \_ -> ret tt)
           (lam $ \_ -> ret tt)

boo :: forall dsl.
       DSL dsl => dsl (Pid RSing -> Process dsl ())
boo = lam $ \p ->
         send p (inl (int 0) :: dsl (Int :+: Int))

main :: IO ()
main = checkerMain (exec $ do r <- newRSing
                              p <- spawn r goo
                              app boo p)
