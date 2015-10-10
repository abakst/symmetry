{-# Language GADTs #-}
{-# Language FlexibleInstances #-}
{-# Language UndecidableInstances #-}
module Language.AST where

import Data.Typeable

data RSing  = RS String 
data RMulti = RM String

data Pid r = Pid r

data Process a
  deriving (Typeable)

instance Functor Process where
  fmap  = undefined
instance Applicative Process where
  pure  = undefined
  (<*>) = undefined

instance Monad Process where
  return = undefined
  (>>=)  = undefined

data Var = V String

data Type t where
  TUnit :: Type ()
  TInt :: Type Int
  TArrow :: Type a -> Type b -> Type (a -> b)
  TProc :: Type a -> Type (Process a)

data Expr t where
  ELit       :: t -> Expr t 
  EVar       :: Var -> Expr a
  EAbs       :: Var -> Expr b -> Expr (a -> b)
  ESpawn     :: Expr RSing -> Expr (Process a) -> Expr (Process (Pid RSing))
  ESpawnMany :: Expr RMulti -> Expr (Process a) -> Expr (Process (Pid RMulti))
  EDoMany    :: Expr (Pid RMulti) -> Expr (Pid RSing -> Process a) -> Expr (Process [a])
  ESend      :: Expr (Pid RSing) -> Expr a -> Expr (Process ()) 
  ERecv      :: Expr (Process a)
  EBind      :: Expr (Process a) -> Expr (a -> Process b) -> Expr (Process b)
  ERet       ::  Expr a -> Expr (Process a)

class Symantics repr where
  -- Value Injection
  tt   :: repr ()
  rep  :: Int -> repr Int
  repS :: String -> repr String

  -- Lambda Calculus
  inl  :: repr a -> repr (Either a b)
  inr  :: repr b -> repr (Either a b)
  pair :: repr a -> repr b -> repr (a, b)
  proj1 :: repr (a, b) -> repr a
  proj2 :: repr (a, b) -> repr b
  match :: repr (Either a b) -> repr (a -> c) -> repr (b -> c) -> repr (Either a b -> c)
  lam  :: (repr a -> repr b) -> repr (a -> b)
  app  :: repr (a -> b) -> repr a -> repr b

  -- Monads
  ret  :: Monad m => repr a -> repr (m a)
  bind :: Monad m => repr (m a) -> repr (a -> m b) -> repr (m b)

  -- Primitives:        
  self :: repr (Process (Pid RSing))
  send :: repr (Pid RSing) -> repr a -> repr (Process ())
  recv :: repr (Process a)

  spawn     :: repr RSing -> repr (Process ()) -> repr (Process (Pid RSing))
  spawnMany :: repr RMulti -> repr Int -> repr (Process ()) -> repr (Process (Pid RMulti))
  doMany    :: repr (Pid RMulti) -> repr (Pid RSing -> Process ()) -> repr (Process ())

  newRSing  :: repr String -> repr (Process RSing)
  newRMulti :: repr String -> repr (Process RMulti)

  exec      :: repr String -> repr (Process a) -> repr a 
