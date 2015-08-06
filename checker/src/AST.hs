{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module AST where

import           Prelude hiding (concatMap, mapM, foldl, concat)  
import           Data.Traversable 
import           Data.Foldable
import           Data.Functor 
import           Control.Applicative
import           Control.Monad.State hiding (mapM)
import           Data.Typeable
import           Data.Generics
import qualified Data.Map.Strict as M
  
data Set = S String
           deriving (Ord, Eq, Read, Show, Typeable, Data)

data Var = V String
           deriving (Ord, Eq, Read, Show, Typeable, Data)
                    
data LVar = LV String
           deriving (Ord, Eq, Read, Show, Typeable, Data)

newtype MTyCon = MTyCon { untycon :: String }
  deriving (Ord, Eq, Read, Show, Typeable, Data)
  
data Pid = PConc Int
         | PAbs { absVar :: Var, absSet :: Set }
         {- These do not appear in configurations: -}
         | PUnfold Var Set Int
         | PVar Var
           deriving (Ord, Eq, Read, Show, Typeable, Data)

isUnfold :: Pid -> Bool
isUnfold (PUnfold _ _ _)  = True
isUnfold _                = False

isAbs :: Pid -> Bool
isAbs (PAbs _ _)        = True
isAbs _                 = False

data MType = MTApp { tycon :: MTyCon
                   , tyargs :: [Pid]
                   }
           deriving (Ord, Eq, Read, Show, Typeable, Data)

data Stmt a = SSkip a
            | SBlock [Stmt a] a
            | SSend Pid [(MType, Stmt a)] a
            | SRecv [(MType, Stmt a)] a
            | SIter Var Set (Stmt a) a
            | SLoop LVar (Stmt a) a
            | SChoose Var Set (Stmt a) a
            | SVar LVar a
            {- These do not appear in the source: -}
            | SVarDecl Var a
            | STest Var a
            | SNonDet [Stmt a]
         deriving (Eq, Read, Show, Functor, Foldable, Data, Typeable)
                  
-- | Unfold
unfold :: Config a -> Config a
unfold c@(Config { cUnfold = us, cProcs = ps })
  = c { cProcs = ps ++ ufprocs }
  where
    mkUnfold v s stmt i = (PUnfold v s i, stmt)
    ufprocs             = [ (mkUnfold v s stmt j) | Conc s i <- us
                                                  , ((PAbs v s'), stmt) <- ps
                                                  , s == s'
                                                  , j <- [0..i-1]]
      
instStmt :: [Pid] -> Stmt a -> Stmt a 
-- Interesting Cases
instStmt dom (SRecv mts a) 
  = SRecv (concatMap (instMS dom) mts) a
instStmt dom (SSend p mts a) 
  = SSend p (concatMap (instMS dom) mts) a
-- Not so interesting cases:
instStmt _ (SSkip a) 
  = SSkip a
instStmt dom (SBlock ss a) 
  = SBlock (map (instStmt dom) ss) a
instStmt dom (SIter v s t a)
  = SIter v s (instStmt dom t) a
instStmt dom (SLoop v s a)
  = SLoop v (instStmt dom s) a
instStmt dom (SChoose v s t a)
  = SChoose v s (instStmt dom t) a
instStmt _ (SVar v a)
  = SVar v a
         
instMS :: [Pid] -> (MType, Stmt a) -> [(MType, Stmt a)]
instMS dom (m@(MTApp _ xs), s) 
  = foldl' doAllSubs [(m,s)] [ v | PVar v <- xs ]
  where
    doAllSubs :: [(MType, Stmt a)] -> Var -> [(MType, Stmt a)]
    doAllSubs ms x = concat [ map (substMS i) ms | i <- subs x ]
    subs :: Var -> [Subst]
    subs x = [ [(x, q)] | q <- dom ]
  
instAbs :: Config a -> Config a       
instAbs c@(Config { cProcs = ps })
  = c { cProcs = map (inst1Abs dom) ps }
  where
    dom                          = map fst ps
    inst1Abs d (p@(PAbs _ _), s) = (p, instStmt d s)
    inst1Abs _ p                 = p

              
-- | Substitution of PidVars for Pids
type Subst = [(Var, Pid)]
  
restrict :: Var -> Subst -> Subst
restrict x s = [(v, q) | (v, q) <- s, v /= x]
  
subst :: Subst -> Stmt a -> Stmt a
subst s (SBlock ss a)    = SBlock (map (subst s) ss) a
subst s (SSend p ms a)   = SSend (substPid s p) (map (substMS s) ms) a
subst s (SRecv ms a)     = SRecv (map (substMS s) ms) a
subst s (SIter v xs t a) = SIter v xs (subst s' t) a
  where s'               = restrict v s
subst s (SLoop v t a)    = SLoop v (subst s t) a
subst _ stmt             = stmt
       
substMS :: Subst -> (MType, Stmt a) -> (MType, Stmt a)        
substMS s (MTApp tc as, t) 
  = (MTApp tc (map (substPid s) as), subst s t)
   
substPid :: Subst -> Pid -> Pid 
substPid s p@(PVar v) = maybe p id $ lookup v s 
substPid _ p          = p
                  

-- | Statement Annotations
annot :: Show a => Stmt a -> a
annot (SSkip a)         = a
annot (SBlock _ a)      = a
annot (SSend _ _ a)     = a
annot (SRecv _ a)       = a
annot (SIter _ _ _ a)   = a
annot (SChoose _ _ _ a) = a
annot (SVar _ a)        = a
annot x                 = error ("annot: TBD " ++ show x)
                          
-- | Typeclass tomfoolery
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
data Unfold = Conc Set Int deriving (Eq, Read, Show, Data, Typeable)

joinMaps :: M.Map Int [a] -> M.Map Int [a] -> M.Map Int [a]       
joinMaps = M.unionWith (++)     
           
addNext :: Int -> [a] -> M.Map Int [a] -> M.Map Int [a]
addNext i is = M.alter (fmap (++is)) i
               
lastStmts :: Stmt a -> [Stmt a]
lastStmts s@(SSkip _)       = [s]
lastStmts s@(SVar _ _)      = [s]
lastStmts (SBlock ss _)     = [last ss]
lastStmts (SSend _ ms _)    = concatMap (lastStmts . snd) ms
lastStmts (SRecv ms _)      = concatMap (lastStmts . snd) ms
lastStmts (SChoose _ _ s _) = lastStmts s
lastStmts (SIter _ _ s _)   = lastStmts s
lastStmts (SLoop _ s _)     = lastStmts s

nextStmts :: Stmt Int -> M.Map Int [Int]
nextStmts (SSend _ ms i)
  = foldl (\m -> joinMaps m . nextStmts) (M.fromList [(i, map (annot . snd) ms)])$ map snd ms
nextStmts (SRecv ms i)
  = foldl (\m -> joinMaps m . nextStmts) (M.fromList [(i, map (annot . snd) ms)])$ map snd ms
nextStmts (SIter _ _ s i) 
  = M.fromList ((i, [annot s]):[(annot j, [i]) | j <- lastStmts s])  `joinMaps` nextStmts s
nextStmts (SLoop v s i)
  = M.fromList ((i, [annot s]):[(j, [i]) | j <- js ]) `joinMaps` nextStmts s
  where
    js = [ j | SVar v' j <- listify (const True) s, v' == v]
nextStmts (SChoose _ _ s i)
  = addNext i [annot s] $ nextStmts s
nextStmts _
  = M.empty
    
data Config a = Config { 
    cTypes  :: [MType]
  , cSets   :: [Set]
  , cUnfold :: [Unfold]
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
