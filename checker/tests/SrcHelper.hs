module SrcHelper where

import Symmetry.Language.AST
import Symmetry.Language.Syntax

any_nat :: Symantics repr => repr (Process Int)
any_nat  = ret (repI 42)

any_list :: Symantics repr => repr (Process [a])
any_list = undefined

id :: Symantics repr => repr (a->a)
id  = lam $ \x -> x

app2 :: Symantics repr => repr (a->b->c) -> repr a -> repr b -> repr c
app2 f a1 a2 = app (app f a1) a2

app3 :: Symantics repr => repr (a->b->c->d) -> repr a -> repr b -> repr c -> repr d
app3 f a1 a2 a3 = app (app (app f a1) a2) a3

app4 :: Symantics repr => repr (a->b->c->d->e) -> repr a -> repr b -> repr c -> repr d -> repr e
app4 f a1 a2 a3 a4 = app (app (app (app f a1) a2) a3) a4

ifte      :: Symantics repr => repr Boolean -> repr a -> repr a -> repr a
ifte b t e = match b (lam $ \_ -> t) (lam $ \_ -> e)
