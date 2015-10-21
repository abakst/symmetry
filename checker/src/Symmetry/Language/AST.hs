{-# LANGUAGE DeriveDataTypeable #-}
{-# Language GADTs #-}
{-# Language FunctionalDependencies #-}
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
  tt   :: repr ()
  int  :: Int    -> repr Int
  str  :: String -> repr String
  bool :: Bool   -> repr Bool

  plus   :: repr Int -> repr Int -> repr Int

  eq   :: (Ord a) => repr a -> repr a -> repr Bool
  gt   :: (Ord a) => repr a -> repr a -> repr Bool
  lt   :: (Ord a) => repr a -> repr a -> repr Bool

  not  :: repr Bool -> repr Bool
  and  :: repr Bool -> repr Bool -> repr Bool
  or   :: repr Bool -> repr Bool -> repr Bool

  nil  :: repr [a]
  cons :: repr a   -> repr [a] -> repr [a]
  hd   :: repr [a] -> repr a
  tl   :: repr [a] -> repr [a]

  -- Lambda Calculus:
  lam  :: (repr a -> repr b) -> repr (a -> b)
  app  :: repr (a -> b) -> repr a -> repr b

  -- Monads:
  ret  :: repr a -> repr (Process repr a)
  bind :: repr (Process repr a) -> repr (a -> Process repr b) -> repr (Process repr b)
  fixM :: repr ((a -> Process repr a) -> a -> Process repr a) -> repr (a -> Process repr a)

  -- Primitives:        
  self      :: repr (Process repr (Pid RSing))
  send :: (Serialize repr a) => repr (Pid RSing) -> repr a -> repr (Process repr ())
  recv :: (Serialize repr a) => repr (Process repr a)

  newRSing  :: repr (Process repr RSing)
  spawn     :: repr RSing -> repr (Process repr ()) -> repr (Process repr (Pid RSing))

  newRMulti :: repr (Process repr RMulti)
  spawnMany :: repr RMulti -> repr Int -> repr (Process repr ()) -> repr (Process repr (Pid RMulti))
  doMany    :: repr (Pid RMulti) -> repr (Pid RSing -> Process repr a) -> repr (Process repr ())

  die       :: repr (Process repr a)

  -- "Run" a process             
  exec      :: repr (Process repr a) -> repr a 

  inl  :: repr a -> repr (a :+: b)
  inr  :: repr b -> repr (a :+: b)
  pair :: repr a -> repr b -> repr (a, b)
  proj1 :: repr (a, b) -> repr a
  proj2 :: repr (a, b) -> repr b

 -- Fold these in???           
  -- t     :: trep a
  -- tjoin :: trep a -> trep a -> trep a 

  -- pat  :: pat a
  -- mcase :: pat a -> rep (a -> c) -> mcase (a -> c)

-- instance SymType repr a  

-- class (Symantics repr, SymPat repr pat a, SymPat repr pat b) => SymMatch repr pat a b c where
--   match :: repr (a :+: b) -> repr (pat repr a -> c) -> repr (pat repr b -> c) -> repr c
-- class (Symantics repr trep pat mcase) => SymMatch trep repr pat mcase c where
--   match :: repr (a :+: b) -> mcase (a -> c) -> mcase (b -> c) -> repr c
class (Symantics repr) => SymMatch repr where
  match :: (Typeable a, Typeable b) => repr (a :+: b) -> repr (a -> c) -> repr (b -> c) -> repr c

class Typeable a => Serialize (f :: * -> *) a where
  data Put f :: *
  data Get f :: * -> *
  put :: f a -> Put f
  get :: Get f a
