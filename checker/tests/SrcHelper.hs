{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SrcHelper where

import Prelude hiding (lookup, fail)

import Symmetry.Language.AST
import Symmetry.Language.Syntax

any_bool :: Symantics repr => repr (() -> Process Boolean)
any_bool  = lam $ \_ -> ret repF

any_nat :: Symantics repr => repr (() -> Process Int)
any_nat  = lam $ \_ -> ret (repI 42)

any_list :: Symantics repr => repr (() -> Process [a])
any_list = lam $ \_ -> ret nil

id :: Symantics repr => repr (a->a)
id  = lam $ \x -> x

app2 :: Symantics repr => repr (a->b->c) -> repr a -> repr b -> repr c
app2 f a1 a2 = app (app f a1) a2

app3 :: Symantics repr => repr (a->b->c->d) -> repr a -> repr b -> repr c -> repr d
app3 f a1 a2 a3 = app (app (app f a1) a2) a3

app4 :: Symantics repr => repr (a->b->c->d->e) -> repr a -> repr b -> repr c -> repr d -> repr e
app4 f a1 a2 a3 a4 = app (app (app (app f a1) a2) a3) a4

app5 :: Symantics repr
     => repr (a->b->c->d->e->f)
     -> repr a -> repr b -> repr c -> repr d -> repr e -> repr f
app5 f a1 a2 a3 a4 a5 = app (app (app (app (app f a1) a2) a3) a4) a5

ifte      :: (Symantics repr, SymMatch repr () () a)
          => repr Boolean -> repr a -> repr a -> repr a
ifte b t e = match b (lam $ \_ -> t) (lam $ \_ -> e)

lookup :: ( Symantics repr
          , SymMatch repr () () (() :+: b)
          , SymTypes repr () b
          , SymTypes repr a b
          , Ord a, Ord b
          )
       => repr (a -> [(a,b)] -> (Either () b))
lookup  = lam $ \k -> lam $ \m ->
            ifte (eq nil m)
              (inl tt)
              (let x  = hd m
                   k' = proj1 x
                   v' = proj2 x
                in ifte (eq k k')
                     (inr v')
                     (app2 lookup k m))

print :: Symantics repr => repr (a -> Process ())
print  = undefined

mod :: Symantics repr => repr (Int -> Int -> Int)
mod  = undefined

match3 :: ( Symantics repr
          , SymMatch repr b c r
          , SymMatch repr a (Either b c) r
          )
       => repr (Either a (Either b c))
       -> repr (a -> r) -> repr (b -> r) -> repr (c -> r)
       -> repr r
match3 msg f1 f2 f3 = match msg f1 $ lam (\e1 -> match e1 f2 f3)

match4 :: ( Symantics repr
          , SymMatch repr c d r
          , SymMatch repr b (Either c d) r
          , SymMatch repr a (Either b (Either c d)) r
          )
       => repr (Either a (Either b (Either c d)))
       -> repr (a -> r) -> repr (b -> r) -> repr (c -> r) -> repr (d -> r)
       -> repr r
match4 msg f1 f2 f3 f4 = match msg f1 $ lam $ \e1 ->
                           match e1 f2 $ lam $ \e2 ->
                             match e2 f3 f4

match5 :: ( Symantics repr
          , SymMatch repr d e r
          , SymMatch repr c (Either d e) r
          , SymMatch repr b (Either c (Either d e)) r
          , SymMatch repr a (Either b (Either c (Either d e))) r
          )
       => repr (Either a (Either b (Either c (Either d e))))
       -> repr (a -> r) -> repr (b -> r) -> repr (c -> r) -> repr (d -> r) -> repr (e -> r)
       -> repr r
match5 msg f1 f2 f3 f4 f5 = match msg f1 $ lam $ \e1 ->
                             match e1 f2 $ lam $ \e2 ->
                               match e2 f3 $ lam $ \e3 ->
                                 match e3 f4 f5

compare :: Symantics repr => repr (a -> a -> (Either () (Either () ())))
compare  = undefined
