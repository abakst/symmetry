{-# LANGUAGE DeriveDataTypeable #-}
{-# Language GADTs #-}
{-# Language FlexibleInstances #-}
{-# Language UndecidableInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language TypeOperators #-}
module Symmetry.Language.AST where

import Data.Either
import Data.Hashable
import Data.Typeable
import Control.Applicative

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

type (:+:) a b = Either a b

class Symantics repr where
  -- Value Injection:
  tt   :: repr ()
  repI :: Int -> repr Int
  repB :: Bool -> repr Bool
  repS :: String -> repr String

  plus :: repr Int -> repr Int -> repr Int

  eq   :: (Ord a) => repr a -> repr a -> repr Bool
  gt   :: (Ord a) => repr a -> repr a -> repr Bool
  lt   :: (Ord a) => repr a -> repr a -> repr Bool

  not  :: repr Bool -> repr Bool
  and  :: repr Bool -> repr Bool -> repr Bool
  or   :: repr Bool -> repr Bool -> repr Bool

  ifte :: repr Bool -> repr a -> repr a -> repr a

  nil  :: repr [a]
  cons :: repr a   -> repr [a] -> repr [a]
  hd   :: repr [a] -> repr a
  tl   :: repr [a] -> repr [a]

  -- Lambda Calculus:
  inl  :: repr a -> repr (Either a b)
  inr  :: repr b -> repr (Either a b)
  pair :: repr a -> repr b -> repr (a, b)
  proj1 :: repr (a, b) -> repr a
  proj2 :: repr (a, b) -> repr b
  match :: repr (Either a b) -> repr (a -> c) -> repr (b -> c) -> repr c
  lam  :: (repr a -> repr b) -> repr (a -> b)
  app  :: repr (a -> b) -> repr a -> repr b

  -- Monads:
  ret  :: repr a -> repr (Process a)
  bind :: repr (Process a) -> repr (a -> Process b) -> repr (Process b)
  fixM :: repr ((a -> Process a) -> a -> Process a) -> repr (a -> Process a)

  -- Primitives:        
  self      :: repr (Process (Pid RSing))
  spawn     :: repr RSing -> repr (Process a) -> repr (Process (Pid RSing))
  spawnMany :: repr RMulti -> repr Int -> repr (Process ()) -> repr (Process (Pid RMulti))
  doMany    :: repr (Pid RMulti) -> repr (Pid RSing -> Process a) -> repr (Process ())
  newRSing  :: repr (Process RSing)
  newRMulti :: repr (Process RMulti)
  die       :: repr (Process a)

  -- "Run" a process             
  exec      :: repr (Process a) -> repr a

class Symantics repr => SymRecv repr a where
  recv :: repr (Process a)

class Symantics repr => SymSend repr a where
  send :: repr (Pid RSing) -> repr a -> repr (Process ())
