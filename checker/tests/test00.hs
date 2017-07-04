{-# Language RebindableSyntax #-}
{-# Language TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}
module Test00 where

import Prelude hiding ((>>=), (>>), fail, return) 
import Symmetry.Language.AST  
import Symmetry.Language.Syntax  
import Symmetry.SymbEx

foo :: SymbEx (Process ())
foo = do p <- recv
         match p (lam $ \pid1 -> app bar pid1)
                 (lam $ \pid2 -> app bar pid2)

bar :: SymbEx (Pid RSing -> Process ())
bar = lam $ \p -> do me <- self
                     send p (inl me :: SymbEx (Pid RSing :+: Pid RSing))

baz :: SymbEx (Process ())
baz = do r <- newRSing
         spawn r foo
         return tt
