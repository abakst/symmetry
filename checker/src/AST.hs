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
import qualified Data.IntMap as M
  
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
            | SVarDecl Var a
            | STest Var a
            | SNonDet [Stmt a]
         deriving (Eq, Read, Show, Functor, Foldable, Traversable, Typeable)
                  
type Process a = (Pid, [Stmt a])

data Config a = Config { 
    cTypes :: [MType]
  , cSets  :: [Set]
  , cProcs :: [Process a]
  } deriving (Eq, Read, Show, Typeable)

-- | Operations
freshId :: Stmt a -> State Int (Stmt Int)
freshId s
  = mapM (const fr) s
  where
    fr = do n <- get
            put (n + 1)
            return n
      
-- buildMap :: Stmt a -> Writer
            

-- nextMap :: [Stmt Int] -> M.IntMap [Int]
-- nextMap ss
--   = mapM go ss
--   where
--     go s
{-
L0:
send;
L1:
recv;
L2:   
for ...:
  L3:
  send; 
  L4:
  recv;
L5:
send;
-}
