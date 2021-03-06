{-# Language RebindableSyntax #-}
module Symmetry.Language.Syntax where

import Prelude (Int)
import Symmetry.Language.AST  

-- Import this module and use with the RebindableSyntax Language extension
(+) :: DSL repr => repr Int -> repr Int -> repr Int
m + n = plus m n

(>>=) :: Symantics repr
      => repr (Process repr a)
      -> (repr a -> repr (Process repr b))
      -> repr (Process repr b)
m >>= f = bind m (lam f)

(>>) :: Symantics repr
      => repr (Process repr a)
      -> repr (Process repr b)
      -> repr (Process repr b)
m >> n = bind m (lam (\_ ->  n))
                 

fail :: Symantics repr => repr (Process repr a)
fail = die

return :: Symantics repr => repr a -> repr (Process repr a)
return = ret

x |> f = app f x
