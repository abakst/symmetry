{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SrcHelper where

import Symmetry.Language.AST
import Symmetry.Language.Syntax

import Prelude hiding (lookup, fail)
import Data.Typeable

any_bool :: Symantics repr => repr (() -> Process repr Boolean)
any_bool  = lam $ \_ -> ret (bool (Left ()))

any_nat :: Symantics repr => repr (() -> Process repr Int)
any_nat  = lam $ \_ -> ret (int 42)

any_list :: Symantics repr => repr (() -> Process repr [Int])
any_list = lam $ \_ -> ret (cons (int 1) (cons (int 2) nil))

id :: Symantics repr => repr (a-> Process repr a)
id  = lam $ \x -> ret x

reject :: Symantics repr => repr (a-> Process repr b)
reject  = lam $ \_ -> fail

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

ifte      :: ( Symantics repr
             , ArbPat repr ()
             , Typeable a
             )
          => repr Boolean -> repr a -> repr a -> repr a
ifte b t e = match b (lam $ \_ -> t) (lam $ \_ -> e)

lookup :: ( Symantics repr
          , ArbPat repr ()
          , Ord a, Ord b, Typeable b
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

print :: Symantics repr => repr (a -> Process repr ())
print  = undefined

mod :: Symantics repr => repr (Int -> Int -> Int)
mod  = undefined

match3 :: ( Symantics repr
          , Typeable a, Typeable b, Typeable c
          , ArbPat repr a
          , ArbPat repr b
          , ArbPat repr c
          )
       => repr (Either a (Either b c))
       -> repr (a -> r) -> repr (b -> r) -> repr (c -> r)
       -> repr r
match3 msg f1 f2 f3 = match msg f1 $ lam (\e1 -> match e1 f2 f3)

match4 :: ( Symantics repr
          , Typeable a, Typeable b, Typeable c, Typeable d
          , ArbPat repr a
          , ArbPat repr b
          , ArbPat repr c
          , ArbPat repr d
          )
       => repr (Either a (Either b (Either c d)))
       -> repr (a -> r) -> repr (b -> r) -> repr (c -> r) -> repr (d -> r)
       -> repr r
match4 msg f1 f2 f3 f4 = match msg f1 $ lam $ \e1 ->
                           match e1 f2 $ lam $ \e2 ->
                             match e2 f3 f4

match5 :: ( Symantics repr
          , Typeable a, Typeable b, Typeable c, Typeable d, Typeable e
          , ArbPat repr a
          , ArbPat repr b
          , ArbPat repr c
          , ArbPat repr d
          , ArbPat repr e
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

ret_tt  :: Symantics repr => repr (Process repr a) -> repr (Process repr ())
ret_tt p = p Symmetry.Language.Syntax.>> ret tt

pair3 :: ( Symantics repr
         )
      => repr a -> repr b -> repr c -> repr (a,(b,c))
pair3 a1 a2 a3 = pair a1 (pair a2 a3)

pair4 :: ( Symantics repr
         )
      => repr a -> repr b -> repr c -> repr d -> repr (a,(b,(c,d)))
pair4 a1 a2 a3 a4 = pair a1 $ pair a2 $ pair a3 a4

pair5 :: ( Symantics repr
         )
      => repr a -> repr b -> repr c -> repr d -> repr e -> repr (a,(b,(c,(d,e))))
pair5 a1 a2 a3 a4 a5 = pair a1 $ pair a2 $ pair a3 $ pair a4 a5
