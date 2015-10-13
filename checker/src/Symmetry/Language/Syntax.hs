{-# Language RebindableSyntax #-}
module Symmetry.Language.Syntax where

import Prelude (error)
import Symmetry.Language.AST  

-- Import this module and use with the RebindableSyntax Language extension

(>>=) :: Symantics repr
      => repr (Process a)
      -> (repr a -> repr (Process b))
      -> repr (Process b)
m >>= f = bind m (lam f)

(>>) :: Symantics repr
      => repr (Process a)
      -> repr (Process b)
      -> repr (Process b)
m >> n = do {_ <- m; n}
                 

fail :: a
fail = error "TBD: Language.Syntax.fail"

return :: Symantics repr => repr a -> repr (Process a)
return = ret
