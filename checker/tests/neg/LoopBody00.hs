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
              p <- spawn r $ loop
              app loop2 p
  where
    loop =  
         do  p <- recv
             match p
               (lam $ \(_ :: dsl ()) -> ret tt)
               (lam $ \(_ :: dsl ()) -> ret tt)

    loop2 = lam $ \p ->
            do me <- self
               (match nondet
                 (lam $ \_ -> send p (inl me :: dsl (Pid RSing :+: ())))
                 (lam $ \_ -> send p (inr tt :: dsl (Pid RSing :+: ()))))
