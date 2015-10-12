{-# Language GADTs #-}
{-# Language FlexibleInstances #-}
{-# Language UndecidableInstances #-}
{-# Language MultiParamTypeClasses #-}
module Language.AST where

import Data.Hashable
import Data.Typeable

data RSing  = RS Int deriving (Eq, Show)
data RMulti = RM Int deriving (Eq, Show)

instance Hashable RSing where
  hashWithSalt s (RS i) = hashWithSalt s i

instance Hashable RMulti where
  hashWithSalt s (RM i) = hashWithSalt s i

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

class Symantics repr where
  -- Value Injection
  tt   :: repr ()
  repI :: Int -> repr Int
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

  -- -- Monads
  ret  :: repr a -> repr (Process a)
  bind :: repr (Process a) -> repr (a -> Process b) -> repr (Process b)

  -- -- Primitives:        
  self :: repr (Process (Pid RSing))
  send :: repr (Pid RSing) -> repr a -> repr (Process ())

  spawn     :: repr RSing -> repr (Process ()) -> repr (Process (Pid RSing))
  spawnMany :: repr RMulti -> repr Int -> repr (Process ()) -> repr (Process (Pid RMulti))
  doMany    :: repr (Pid RMulti) -> repr (Pid RSing -> Process ()) -> repr (Process ())

  newRSing  :: repr (Process RSing)
  newRMulti :: repr (Process RMulti)

  exec      :: repr String -> repr (Process a) -> repr a 

class Symantics repr => SymRecv repr a where
  recv :: repr (Process a)
