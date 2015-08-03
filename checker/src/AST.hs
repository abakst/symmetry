{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module AST where

import           Prelude hiding (mapM)  
import           Data.Traversable
import           Data.Foldable
import           Data.Functor
import           Control.Applicative
import           Control.Monad.State hiding (mapM)
import           Data.Typeable
import           Data.Generics
  
data Set = S String
           deriving (Ord, Eq, Read, Show, Typeable, Data)

data Var = V String
           deriving (Ord, Eq, Read, Show, Typeable, Data)

newtype MTyCon = MTyCon { untycon :: String }
  deriving (Ord, Eq, Read, Show, Typeable, Data)
  
data Pid = PConc Int
         | PAbs { absVar :: Var, absSet :: Set }
         | PVar Var
           deriving (Ord, Eq, Read, Show, Typeable, Data)

data MType = MTApp { tycon :: MTyCon
                   , tyargs :: [Pid]
                   }
           deriving (Ord, Eq, Read, Show, Typeable, Data)

data Stmt a = SSkip a
            | SBlock [Stmt a] a
            | SSend Pid [(MType, Stmt a)] a
            | SRecv [(MType, Stmt a)] a
            | SIter Var Set (Stmt a) a
            | SLoop Var (Stmt a) a
            | SChoose Var Set (Stmt a) a
            | SVar Var a
            {- These do not appear in the source: -}
            | SVarDecl Var a
            | STest Var a
            | SNonDet [Stmt a]
         deriving (Eq, Read, Show, Functor, Foldable, Data, Typeable)
                  
instance Traversable Stmt where
  traverse f (SSkip a) 
    = SSkip <$> f a
  traverse f (SSend p ms a) 
    = flip (SSend p) <$> f a <*> traverse (traverse (traverse f)) ms
  traverse f (SRecv ms a)
    = flip SRecv <$> f a <*> traverse (traverse (traverse f)) ms
  traverse f (SIter v s ss a) 
    = flip (SIter v s) <$> f a <*> (traverse f) ss
  traverse f (SLoop v ss a) 
    = flip (SLoop v) <$> f a <*> (traverse f) ss
  traverse f (SChoose v s ss a) 
    = flip (SChoose v s) <$> f a <*> (traverse f) ss
  traverse f (SVar v a)
    = SVar v <$> f a
  traverse f (SBlock ss a)
    = flip SBlock <$> f a <*> traverse (traverse f) ss
  traverse _ _
    = error "traverse undefined for non-source stmts"
    
type Process a = (Pid, Stmt a)

data Config a = Config { 
    cTypes  :: [MType]
  , cSets   :: [Set]
  , cUnfold :: [Pid]
  , cProcs  :: [Process a]
  } deriving (Eq, Read, Show, Typeable)

-- | Operations
freshId :: Stmt a -> State Int (Stmt Int)
freshId s
  = mapM (const fr) s
  where
    fr = do n <- get
            put (n + 1)
            return n
                   
freshIds :: Stmt a -> Stmt Int
freshIds ss = evalState (freshId ss) 1
