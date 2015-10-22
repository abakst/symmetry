{-# LANGUAGE DeriveDataTypeable #-}
{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language UndecidableInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language TypeOperators #-}
{-# Language StandaloneDeriving #-}
{-# Language TypeFamilies #-}
module Symmetry.Language.AST where

import Data.Hashable
import Data.Typeable

data RSing  = RS Int deriving (Ord, Eq, Show, Typeable)
data RMulti = RM Int deriving (Ord, Eq, Show, Typeable)

instance Hashable RSing where
  hashWithSalt s (RS i) = hashWithSalt s i

instance Hashable RMulti where
  hashWithSalt s (RM i) = hashWithSalt s i

data Pid r = Pid r deriving (Typeable)

deriving instance Eq a  => Eq (Pid a)
deriving instance Ord a => Ord (Pid a)

type (:+:) a b = Either a b

type Boolean = Either () ()  -- Either True False

class Symantics repr where
  -- Process Type
  data Process repr :: * -> *
  -- Value Injection:
  tt     :: repr ()
  int    :: Int     -> repr Int
  str    :: String  -> repr String
  bool   :: Boolean -> repr Boolean
  nondet :: repr Boolean

  plus   :: repr Int -> repr Int -> repr Int

  eq   :: (Ord a) => repr a -> repr a -> repr Boolean
  gt   :: (Ord a) => repr a -> repr a -> repr Boolean
  lt   :: (Ord a) => repr a -> repr a -> repr Boolean

  not  :: repr Boolean -> repr Boolean
  and  :: repr Boolean -> repr Boolean -> repr Boolean
  or   :: repr Boolean -> repr Boolean -> repr Boolean

  -- Lists
  nil       :: repr [a]
  cons      :: repr a   -> repr [a] -> repr [a]
  matchList :: repr [a] -> repr (() -> b) -> repr ((a, [a]) -> b) -> repr b

  -- Lambda Calculus:
  lam  :: (repr a -> repr b) -> repr (a -> b)
  app  :: repr (a -> b) -> repr a -> repr b

  -- Monads:
  ret  :: repr a -> repr (Process repr a)
  bind :: repr (Process repr a) -> repr (a -> Process repr b) -> repr (Process repr b)
  fixM :: repr ((a -> Process repr a) -> a -> Process repr a) -> repr (a -> Process repr a)

  -- Primitives:        
  self      :: repr (Process repr (Pid RSing))
  send :: (Typeable a) => repr (Pid RSing) -> repr a -> repr (Process repr ())
  recv :: (Typeable a, ArbPat repr a) => repr (Process repr a)

  newRSing  :: repr (Process repr RSing)
  spawn     :: repr RSing -> repr (Process repr ()) -> repr (Process repr (Pid RSing))

  newRMulti :: repr (Process repr RMulti)
  spawnMany :: repr RMulti -> repr Int -> repr (Process repr ()) -> repr (Process repr (Pid RMulti))
  doMany    :: repr (Pid RMulti) -> repr (Pid RSing -> Process repr a) -> repr (Process repr ())

  die       :: repr (Process repr a)

  -- "Run" a process             
  exec      :: repr (Process repr a) -> repr a 

  inl   :: repr a -> repr (a :+: b)
  inr   :: repr b -> repr (a :+: b)
  pair  :: repr a -> repr b -> repr (a, b)
  proj1 :: repr (a, b) -> repr a
  proj2 :: repr (a, b) -> repr b

  match :: (Typeable a, Typeable b, ArbPat repr a, ArbPat repr b)
        => repr (a :+: b) -> repr (a -> c) -> repr (b -> c) -> repr c

class Pat pat where
  joinPat  :: pat a -> pat a -> pat a
  liftPat1 :: pat a -> pat (a :+: b)
  liftPat2 :: pat b -> pat (a :+: b)

class Pat pat => ArbPat pat a where
  arb   :: pat a

instance (ArbPat arb a, ArbPat arb b) => ArbPat arb (a :+: b) where
  arb  = liftPat1 arb `joinPat` liftPat2 arb

instance (Symantics arb, ArbPat arb a, ArbPat arb b) => ArbPat arb (a, b) where
  arb  = pair arb arb

class (Symantics repr,
       ArbPat repr (),
       ArbPat repr Int,
       ArbPat repr String,
       ArbPat repr (Pid RSing)) => DSL repr where         

instance (Symantics repr,
          ArbPat repr (),
          ArbPat repr Int,
          ArbPat repr String,
          ArbPat repr (Pid RSing)) => DSL repr where
