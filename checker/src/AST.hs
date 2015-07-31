{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module AST where
  
import Data.Traversable
import Data.Foldable
import Data.Functor
import Control.Applicative
import Data.Typeable
  
data Set = S String
           deriving (Ord, Eq, Read, Show)

data Var = V String
           deriving (Ord, Eq, Read, Show)

newtype MTyCon = MTyCon { untycon :: String }
  deriving (Ord, Eq, Read, Show)

data MType = MTApp { tycon :: MTyCon
                   , tyargs :: [Pid]
                   }
           deriving (Ord, Eq, Read, Show)
  
data Pid = PConc Int
         | PAbs Var Set
         | PVar Var
           deriving (Ord, Eq, Read, Show, Typeable)

data Stmt a = SSkip a
            | SSend Pid [(MType, [Stmt a])] a
            | SRecv [(MType, [Stmt a])] a
            | SIter Var Set [Stmt a] a
            | SLoop Var [Stmt a] a
            | SChoose Var Set [Stmt a] a
            | SVar Var a
            {- These do not appear in the source: -}
            | SVarDecl Var
            | STest Var
            | SNonDet [Stmt a]
         deriving (Eq, Read, Show, Functor, Foldable, Typeable)
                  
type Process a = (Pid, [Stmt a])

data Config a = Config { 
    cTypes :: [MType]
  , cSets  :: [Set]
  , cProcs :: [Process a]
  } deriving (Eq, Read, Show, Typeable)
