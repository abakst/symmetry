{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module AST where
  
import Data.Traversable
import Data.Foldable
import Data.Functor
import Control.Applicative
  
data Set = S String
           deriving (Eq, Show)

data Var = V String
           deriving (Eq, Show)

newtype MTyCon = MTyCon { untycon :: String }
  deriving (Eq, Show)

data MType = MTApp { tycon :: MTyCon
                   , tyargs :: [Pid]
                   }
           deriving (Eq, Show)
  
data Pid = PConc Int
         | PAbs Var Set
         | PVar Var
           deriving (Eq, Show)

data Stmt a = SSkip a
            | SSend Pid MType a
            | SRecv MType a
            | SIter Var Set [Stmt a] a
         deriving (Eq, Show, Functor, Foldable)
                  
type Process a = (Pid, [Stmt a])
type Config a = ([MType], [Process a])

instance Traversable Stmt where
  traverse f (SSkip a)      = SSkip <$> f a 
  traverse f (SSend x y a)  = SSend x y <$> f a
  traverse f (SRecv x a)    = SRecv x <$> f a
  traverse f (SIter x y ss a) = SIter x y <$> traverse (traverse f) ss 
                                      <*> f a
