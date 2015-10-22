{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

main :: IO ()
main = checkerMain $ exec mainProc

mainProc :: forall dsl. DSL dsl => dsl (Process dsl ())
mainProc = do r <- newRSing
              p <- spawn r $ app (fixM loop) tt
              f <- app loop2 p
              tt |> fixM f
  where
    loop = lam $ \f -> lam $ \_ -> 
         do  p <- recv
             match p
               (lam $ \pid -> send pid tt >>= app f)
               (lam $ \(_ :: dsl ()) -> ret tt)

    loop2 = lam $ \p ->
              do me <- self
                 ret (lam $ \f -> lam $ \_ ->
                          match nondet
                             (lam $ \_ -> send p (inl me :: dsl (Pid RSing :+: ())) >>= app f)
                             (lam $ \_ -> ret tt))
