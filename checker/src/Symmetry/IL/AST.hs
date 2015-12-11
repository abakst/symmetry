{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Symmetry.IL.AST where

import           Prelude hiding (concatMap, mapM, foldl, concat)
import           Data.Traversable
import           Data.Foldable
import           Control.Monad.State hiding (mapM)
import           Data.Typeable
import           Data.Generics
import           Data.List (nub, isPrefixOf, (\\))
import qualified Data.Map.Strict as M
import Text.PrettyPrint.Leijen as P hiding ((<$>))

setSize :: Int
setSize = 1

infty :: Int
infty = 2

data Set = S String
         | SV String
         | SInts Int
           deriving (Ord, Eq, Read, Show, Typeable, Data)

data Var = V String
           deriving (Ord, Eq, Read, Show, Typeable, Data)

data LVar = LV { unlv :: String }
           deriving (Ord, Eq, Read, Show, Typeable, Data)

newtype MTyCon = MTyCon { untycon :: String }
  deriving (Ord, Eq, Read, Show, Typeable, Data)

data Pid = PConc Int
         | PAbs { absVar :: Var, absSet :: Set }
         {- These do not appear in configurations: -}
         | PUnfold Var Set Int
         | PVar Var
           deriving (Ord, Eq, Read, Show, Typeable, Data)

type PidMap  = M.Map Pid (Int, Int)
type Channel = (Pid, Pid, MTyCon)

isUnfold :: Pid -> Bool
isUnfold PUnfold{} = True
isUnfold _         = False

isAbs :: Pid -> Bool
isAbs (PAbs _ _) = True
isAbs _          = False

isBounded :: [SetBound] -> Pid -> Bool
isBounded bs (PAbs _ s) = s `elem` [ s' | Bounded s' _ <- bs ]
isBounded _ _           = False

data Label = LL | RL | VL Var
             deriving (Ord, Eq, Read, Show, Typeable, Data)

data ILType = TUnit | TInt | TPid | TProd ILType ILType | TSum ILType ILType                      
             deriving (Ord, Eq, Read, Show, Typeable, Data)

data ILPat = PUnit
           | PInt Var
           | PPid Var
           | PProd ILPat ILPat
           | PSum  ILPat ILPat
             deriving (Ord, Eq, Read, Show, Typeable, Data)

data ILExpr = EUnit
            | EInt           
            | EPid Pid
            | EVar Var
            | ELeft ILExpr
            | ERight ILExpr
            | EPair ILExpr ILExpr
             deriving (Ord, Eq, Read, Show, Typeable, Data)

-- send(p, EPid p)                      

data MConstr = MTApp  { tycon :: MTyCon, tyargs :: [Pid] }
             | MCaseL Label MConstr
             | MCaseR Label MConstr
             -- | MTSum MConstr MConstr
             | MTProd { proj1 :: MConstr, proj2 :: MConstr }
             deriving (Ord, Eq, Read, Show, Typeable, Data)

eqConstr :: MConstr -> MConstr -> Bool
eqConstr (MCaseL _ c) (MCaseL _ c')      = eqConstr c c'
eqConstr (MCaseR _ c) (MCaseR _ c')      = eqConstr c c'
eqConstr (MTProd p1 p2) (MTProd p1' p2') = eqConstr p1 p1' && eqConstr p2 p2'
eqConstr a1@(MTApp{}) a2@MTApp{}         = tycon a1 == tycon a2 &&
                                           length (tyargs a1) == length (tyargs a2)
eqConstr _ _                             = False

lookupConstr :: MType -> MConstr -> Maybe CId
lookupConstr m c
  = M.foldlWithKey go Nothing m
  where
    go Nothing i c' = if eqConstr c c' then Just i else Nothing
    go a       _ _  = a

lookupType :: MTypeEnv -> MType -> Maybe TId
lookupType m t
  = M.foldlWithKey go Nothing m
  where
    go Nothing i t' = if t == t' then Just i else Nothing
    go a       _ _  = a

type TId     = Int
type CId     = Int
type VId     = Int
type MType   = M.Map CId MConstr
type MValMap = M.Map MConstr VId -- No variables

type MTypeEnv = M.Map TId MType

data Stmt a = SSkip { annot :: a }

            | SBlock { blkBody :: [Stmt a]
                     , annot :: a
                     }

            | SSend  { sndPid :: ILExpr-- Pid
                     , sndMsg :: (ILType, ILExpr)
                     , annot  :: a
                     }

            | SRecv  { rcvMsg :: (ILType, Var)
                     , annot  :: a
                     }

            | SIter { iterVar  :: Var
                    , iterSet  :: Set
                    , iterBody :: Stmt a
                    , annot    :: a
                    }

            {-used to create a loop with the given label-}
            | SLoop { loopVar  :: LVar
                    , loopBody :: Stmt a
                    , annot    :: a
                    }

            | SChoose { chooseVar :: Var
                      , chooseSet :: Set
                      , chooseBody :: Stmt a
                      , annot      :: a
                      }

            | SVar { varVar :: LVar
                   , annot  :: a
                   }

             -- x := p1 == p2;
            | SCompare { compareVar :: Var
                       , compareLhs :: Pid
                       , compareRhs :: Pid
                       , annot      :: a
                       }

            | SCase { caseVar   :: Var
                    , caseLeft  :: Stmt a
                    , caseRight :: Stmt a
                    , annot     :: a
                    }

            | SNonDet { nonDetBody :: [Stmt a]
                      , annot      :: a
                      }
            | SDie { annot :: a }
            {- These do not appear in the source: -}
            | SNull { annot :: a }
            -- | SVarDecl Var a
            -- | STest Var a
         deriving (Eq, Read, Show, Functor, Foldable, Data, Typeable)

data SetBound = Bounded Set Int
                deriving (Eq, Read, Show, Typeable)
type Process a = (Pid, Stmt a)
data Unfold = Conc Set Int deriving (Eq, Read, Show, Data, Typeable)

data Config a = Config {
    cTypes   :: MTypeEnv
  , cGlobals :: [Var]
  , cGlobalSets :: [Set]
  , cSets    :: [SetBound]
  , cUnfold  :: [Unfold]
  , cProcs   :: [Process a]
  } deriving (Eq, Read, Show, Typeable)

unboundVars :: forall a. Data a => Stmt a -> [Var]
unboundVars s
  = allvars \\ (bound ++ absIdx)
  where
    allvars = nub $ listify (const True :: Var -> Bool) s
    bound   = nub $ everything (++) (mkQ [] go) s
    absIdx  = nub $ everything (++) (mkQ [] goAbs) s
    go :: Data a => Stmt a -> [Var]
    go (SRecv (_,x) _) = [x]
    go (i@SIter {})    = [iterVar i]
    go (i@SChoose {})  = [chooseVar i]
    go _               = []
    goAbs :: Pid -> [Var]
    goAbs (PAbs v _) = [v]
    goAbs _          = []

unboundSets :: forall a. Data a => Stmt a -> [Set]
unboundSets s
  = allSetVars \\ boundSetVars
  where
    allSetVars = nub $ listify isSetVar s
    isSetVar (SV _)      = True
    isSetVar _           = False
    boundSetVars         = nub $ everything (++) (mkQ [] go) s
    go :: Data a => Stmt a -> [Set]
    go (SRecv (_,_) _)   = []
    go _                 = []

endLabels :: (Data a, Typeable a) => Stmt a -> [LVar]
endLabels = nub . listify (isPrefixOf "end" . unlv)

isBound :: Set -> [SetBound] -> Bool
isBound s = any p
  where p (Bounded s' _) = s == s'

boundAbs :: Config a -> Config a
boundAbs c@(Config {cProcs = ps, cSets = bs})
  = c { cUnfold = us }
  where
    us = [ Conc s n | (PAbs _ s, _) <- ps , Bounded s' n <- bs , s == s']

vars :: ILPat -> [Var]
vars = nub . listify (const True)

-- pvars :: MConstr -> [Var]
-- pvars
-- pvars (MTApp _ xs)   = [v | PVar v <- xs]
-- pvars (MCaseL _ c)   = pvars c
-- pvars (MCaseR _ c)   = pvars c
-- pvars (MTProd c1 c2) = nub (pvars c1 ++ pvars c2)

-- lvars ::  -> [Var]
-- lvars (MTApp _ _)       = []
-- lvars (MCaseL (VL l) c) = l : lvars c
-- lvars (MCaseR (VL l) c) = l : lvars c
-- lvars (MCaseL _ c)      = lvars c
-- lvars (MCaseR _ c)      = lvars c
-- lvars (MTProd c1 c2)    = nub (lvars c1 ++ lvars c2)

-- | Typeclass tomfoolery
instance Traversable Stmt where
  traverse f (SSkip a)
    = SSkip <$> f a
  traverse f (SSend p ms a)
    = SSend p ms <$> f a
  traverse f (SRecv ms a)
    = SRecv ms <$> f a
  traverse f (SIter v s ss a)
    = flip (SIter v s) <$> f a <*> traverse f ss
  traverse f (SLoop v ss a)
    = flip (SLoop v) <$> f a <*> traverse f ss
  traverse f (SChoose v s ss a)
    = flip (SChoose v s) <$> f a <*> traverse f ss
  traverse f (SVar v a)
    = SVar v <$> f a
  traverse f (SCompare v p1 p2 a)
    = SCompare v p1 p2 <$> f a
  traverse f (SDie a)
    = SDie <$> f a
  traverse f (SBlock ss a)
    = flip SBlock <$> f a <*> traverse (traverse f) ss
  traverse f (SCase v sl sr a)
    = mkCase <$> f a <*> traverse f sl <*> traverse f sr
    where
      mkCase a l r = SCase v l r a
  traverse f (SNonDet ss a)
    = flip SNonDet <$> f a <*> traverse (traverse f) ss
  traverse _ _
    = error "traverse undefined for non-source stmts"

joinMaps :: M.Map Int [a] -> M.Map Int [a] -> M.Map Int [a]
joinMaps = M.unionWith (++)

addNext :: Int -> [a] -> M.Map Int [a] -> M.Map Int [a]
addNext i is = M.alter (fmap (++is)) i

stmt :: (TId, [(CId, MConstr)], Stmt a) -> Stmt a
stmt (_,_,s) = s

lastStmts :: Stmt a -> [Stmt a]
lastStmts s@(SSkip _)       = [s]
lastStmts s@(SVar _ _)      = [s]
lastStmts s@(SCompare _ _ _ _) = [s]
lastStmts (SBlock ss _)     = [last ss]
lastStmts s@(SSend _ _ _)    = [s]
lastStmts s@(SRecv _ _)      = [s]
lastStmts s@(SNonDet ss _)   = concatMap lastStmts ss
lastStmts (SChoose _ _ s _) = lastStmts s
lastStmts s@(SIter _ _ _ _) = [s]
lastStmts (SLoop _ s _)     = lastStmts s
lastStmts (SCase _ sl sr _) = lastStmts sl ++ lastStmts sr
lastStmts s@(SDie a)        = [s]

nextStmts :: Stmt Int -> M.Map Int [Int]
nextStmts (SNonDet ss i)
  = foldl' (\m -> joinMaps m . nextStmts)
           (M.fromList [(i, map annot ss)])
           ss
nextStmts (SBlock ss i)
  = M.unionsWith (++) (seqstmts : ssnext)
    where
      ssnext   = map nextStmts ss
      seqstmts = M.fromList . fst $ foldl' go ([], [i]) ss
      go (m, is) s = ([(a, [annot s]) | a <- is] ++ m, map annot (lastStmts s))

nextStmts (SIter _ _ s i)
  = M.fromList ((i, [annot s]):[(annot j, [i]) | j <- lastStmts s])  `joinMaps` nextStmts s
nextStmts (SLoop v s i)
  = M.fromList ((i, [annot s]):[(j, [i]) | j <- js ]) `joinMaps` nextStmts s
  where
    js = [ j | SVar v' j <- listify (const True) s, v' == v]
nextStmts (SChoose _ _ s i)
  = addNext i [annot s] $ nextStmts s
nextStmts (SCase _ sl sr i)
  = M.fromList [(i, [annot sl, annot sr])] `joinMaps` nextStmts sl `joinMaps` nextStmts sr
nextStmts _
  = M.empty

-- | Operations
freshId :: Stmt a -> State Int (Stmt Int)
freshId
  = mapM (const fr)
  where
    fr = do n <- get
            put (n + 1)
            return n

freshStmtIds :: Stmt a -> Stmt Int                   
freshStmtIds s = evalState (freshId s) 0

freshIds :: Config a -> Config Int
freshIds (c @ Config { cProcs = ps })
  = c { cProcs = evalState (mapM (mapM freshId) ps) 1 }

instance Pretty Var where
  pretty (V x) = text x

instance Pretty Set where
  pretty (S x)   = text x
  pretty (SV x)  = text x
  pretty (SInts n) = brackets (int 1 <+> text ".." <+> int n)

instance Pretty Pid where
  pretty (PConc x)
    = text "pid@" <> int x
  pretty (PAbs v vs)
    = text "pid@(" <> pretty v <> colon <> pretty vs <> text ")"
  pretty (PVar v)
    = pretty v
  pretty (PUnfold _ s i)
    = text "pid@" <> pretty s <> brackets (int i)

x $$ y  = (x <> line <> y)

instance Pretty Label where
  pretty LL     = text "inl"
  pretty RL     = text "inr"
  pretty (VL x) = pretty x

instance Pretty MConstr where
  pretty (MTApp tc [])   = text (untycon tc)
  pretty (MTApp tc args) = text (untycon tc) <> pretty args
  pretty (MCaseL l t)    = pretty l <+> pretty t
  pretty (MCaseR l t)    = pretty l <+> pretty t
  pretty (MTProd t1 t2)  = parens (pretty t1 <> text ", " <> pretty t2)

instance Pretty ILExpr where
  pretty EUnit     = text "()"
  pretty EInt      = text "int"
  pretty (EVar v)  = pretty v
  pretty (EPid p)  = pretty p
  pretty (ELeft  e) = text "inl" <> parens (pretty e)
  pretty (ERight e) = text "inr" <> parens (pretty e)
  pretty (EPair e1 e2) = tupled [pretty e1, pretty e2]

instance Pretty ILPat where
  pretty (PUnit )      = text "()"
  pretty (PInt v)      = text "int" <+> pretty v
  pretty (PPid v)      = text "pid" <+> pretty v
  pretty (PSum p1 p2)  = parens (pretty p1 <+> text "+" <+> pretty p2)
  pretty (PProd p1 p2) = parens (pretty p1 <+> text "*" <+> pretty p2)

instance Pretty ILType where
  pretty TUnit     = text "()"
  pretty TInt      = text "int"
  pretty TPid      = text "pid"
  pretty (TSum p1 p2)  = parens (pretty p1 <+> text "+" <+> pretty p2)
  pretty (TProd p1 p2) = parens (pretty p1 <+> text "*" <+> pretty p2)

instance Pretty (Stmt a) where
  pretty (SSkip _)
    = text "<skip>"

  pretty (SSend p (t,e) _)
    = text "send" <+> pretty p <+> parens (pretty e <+> text "::" <+> pretty t)

  pretty (SRecv (t,x) _)
    = text "recv" <+> parens (pretty x <+> text "::" <+> pretty t)

  pretty (SIter x xs s _)
    = text "for" <+> parens (pretty x <+> colon <+> pretty xs) <+> lbrace $$
      (indent 2 $ pretty s) $$
      rbrace

  pretty (SVar (LV v) _)
    = text "goto" <+> pretty v

  pretty (SLoop (LV v) s _)
    = pretty v <> colon <+> parens (pretty s)

  pretty (SCase l sl sr _)
    = text "match" <+> pretty l <+> text "with" $$
      indent 2
        (align (vcat [text "| InL ->" <+> pretty sl,
                     text "| InR ->"  <+> pretty sr]))

  pretty (SChoose v r s _)
    = text "select" <+> pretty v <+>
      text "from" <+> pretty r <+>
      text "in" $$ indent 2 (align (pretty s))

  pretty (SDie _)
    = text "CRASH"

  pretty (SBlock ss _)
    = braces (line <> indent 2 (vcat $ punctuate semi (map pretty ss)) <> line)

  pretty (SCompare v p1 p2 _)
    = pretty v <+> colon <> equals <+> pretty p1 <+> equals <> equals <+> pretty p2

  pretty (SNonDet ss _)
    = pretty ss

  pretty (SNull _)
    = text "<null>"

prettyMsg :: (TId, CId, MConstr) -> Doc
prettyMsg (t, c, v)
  = text "T" <> int t <> text "@" <>
    text "C" <> int c <> parens (pretty v)

instance Pretty (Config a) where
  pretty (Config {cProcs = ps, cSets = bs, cGlobals = gs, cGlobalSets = gsets})
    = vcat (map goGlob gs) <$$> 
      vcat (map goGlobS gsets) <$$> 
      vcat (map goB bs) <$$>
      vcat (map go ps)
    where
      goGlob v  = text "Global" <+> pretty v
      goGlobS s = text "Global" <+> pretty s
      goB (Bounded s n) = text "|" <> pretty s <> text "|" <+> equals <+> int n
      go (pid, s) = text "Proc" <+> parens (pretty pid) <> colon <$$>
                    indent 2 (pretty s)
