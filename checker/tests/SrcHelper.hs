module SrcHelper where

import Symmetry.Language.AST
import Symmetry.Language.Syntax

any_nat :: Symantics repr => repr (Process Int)
any_nat  = ret (repI 42)

any_list :: Symantics repr => repr (Process [a])
any_list = undefined

id :: Symantics repr => repr (a->a)
id  = lam $ \x -> x
