{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}
{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language UndecidableInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language TypeOperators #-}
{-# Language StandaloneDeriving #-}
{-# Language TypeFamilies #-}
{-# Language ImplicitParams #-}
module Symmetry.Language.AST where

import Data.Typeable
import GHC.TypeLits
import GHC.Stack

data RSing  = RS Int
            | RSelf Role
            | RElem RMulti
              deriving (Ord, Eq, Show, Typeable)

data RMulti = RM Int deriving (Ord, Eq, Show, Typeable)

data Role = S RSing
          | M RMulti
            deriving (Ord, Eq, Show)

data Pid r = Pid r deriving (Typeable, Show)

deriving instance Eq a  => Eq (Pid a)
deriving instance Ord a => Ord (Pid a)

type (:+:) a b = Either a b

type Boolean = Either () ()  -- Either True False
newtype T (n::Symbol) a = T a deriving Typeable
data TyName (n::Symbol) = TyName

class Symantics repr where
  -- Process Type
  data Process repr :: * -> *
  -- Value Injection:
  tt     :: repr ()
  int    :: Int     -> repr Int
  str    :: String  -> repr String
  bool   :: Boolean -> repr Boolean
  nondetPos :: repr Int
  nondetVal :: repr a -> repr a -> repr (Process repr a)

  neg    :: repr Int -> repr Int
  plus   :: repr Int -> repr Int -> repr Int

  eq   :: Eq a => repr a -> repr a -> repr Boolean
  gt   :: repr Int -> repr Int -> repr Boolean
  lt   :: repr Int -> repr Int -> repr Boolean

  not  :: repr Boolean -> repr Boolean
  and  :: repr Boolean -> repr Boolean -> repr Boolean
  or   :: repr Boolean -> repr Boolean -> repr Boolean

  -- Lists
  nil       :: repr [a]
  cons      :: repr a   -> repr [a] -> repr [a]

  -- Lambda Calculus:
  lam  :: (repr a -> repr b) -> repr (a -> b)
  app  :: repr (a -> b) -> repr a -> repr b

  -- "Types"
  lift   :: (Typeable a, KnownSymbol n) => TyName n -> repr a -> repr (T (n :: Symbol) a)
  forget :: repr (T (n::Symbol) a) -> repr a
                     
  inl   :: repr a -> repr (a :+: b)
  inr   :: repr b -> repr (a :+: b)
  pair  :: repr a -> repr b -> repr (a, b)
  proj1 :: repr (a, b) -> repr a
  proj2 :: repr (a, b) -> repr b

  match :: (?callStack :: CallStack, Typeable a, Typeable b, ArbPat repr a, ArbPat repr b)
        => repr (a :+: b) -> repr (a -> c) -> repr (b -> c) -> repr c
  matchList :: (?callStack :: CallStack, Typeable a, ArbPat repr a)
            => repr [a] -> repr (() -> b) -> repr ((a, [a]) -> b) -> repr b

  -- Monads:
  ret  :: repr a -> repr (Process repr a)
  bind :: repr (Process repr a) -> repr (a -> Process repr b) -> repr (Process repr b)
  fixM :: (?callStack :: CallStack)
       => repr ((a -> Process repr a) -> a -> Process repr a) -> repr (a -> Process repr a)

  -- Primitives:        
  self      :: repr (Process repr (Pid RSing))
  send      :: (?callStack :: CallStack, Typeable a)
            => repr (Pid RSing) -> repr a -> repr (Process repr ())
  recv      :: (?callStack :: CallStack, Typeable a, ArbPat repr a)
            => repr (Process repr a)

  newRSing  :: (?callStack :: CallStack)
            => repr (Process repr RSing)
  spawn     :: (?callStack :: CallStack)
            => repr RSing -> repr (Process repr ()) -> repr (Process repr (Pid RSing))
  newRMulti :: (?callStack :: CallStack)
            => repr (Process repr RMulti)
  spawnMany :: (?callStack :: CallStack)
            => repr RMulti -> repr Int -> repr (Process repr ()) -> repr (Process repr (Pid RMulti))
  doMany    :: String -> repr (Pid RMulti) -> repr (Pid RSing -> Process repr a) -> repr (Process repr [a])
  doN       :: String -> repr Int -> repr (Int -> Process repr a) -> repr (Process repr [a])
  lookup    :: repr (Pid RMulti) -> repr Int -> repr (Pid RSing)
  forever   :: repr (Process repr ()) -> repr (Process repr ())

  die       :: repr (Process repr a)

  -- Verification Primitives:        
  assert     :: repr Boolean -> repr (Process repr ())
  readGhost  :: repr (Pid r) -> String -> repr (Process repr Int)
  readPtrR   :: Typeable a => repr a -> repr (Process repr Int)
  readPtrW   :: Typeable a => repr a -> repr (Process repr Int)
  readMyIdx  :: repr (Process repr Int)


  -- "Run" a process             
  exec      :: repr (Process repr a) -> repr a 

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

instance (Typeable a, Symantics arb, KnownSymbol t, ArbPat arb a) => ArbPat arb (T t a) where
  arb  = lift (TyName :: TyName t) v
    where
      v = arb

class (Symantics repr,
       ArbPat repr (),
       ArbPat repr Int,
       ArbPat repr String,
       ArbPat repr (Pid RSing),
       ArbPat repr (Pid RMulti)
      ) => DSL repr where         

instance (Symantics repr,
          ArbPat repr (),
          ArbPat repr Int,
          ArbPat repr String,
          ArbPat repr (Pid RSing),
          ArbPat repr (Pid RMulti)
         ) => DSL repr where
