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
import qualified Data.IntMap     as I
import Text.PrettyPrint.Leijen as P hiding ((<$>))

setSize :: Int
setSize = 1

infty :: Int
infty = 2

data Set = S String
         | SV String
         | SInts Int
           deriving (Ord, Eq, Read, Show, Typeable, Data)

data Var = V String  -- Local Var
         | GV String -- Global Var
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
isBounded bs (PAbs _ s) = s `elem` [ s' | Known s' _ <- bs ]
isBounded _ _           = False

data Label = LL | RL | VL Var
             deriving (Ord, Eq, Read, Show, Typeable, Data)

data ILType = TUnit | TInt | TString | TPid | TProd ILType ILType | TSum ILType ILType                      
             deriving (Ord, Eq, Read, Show, Typeable, Data)

data ILPat = PUnit
           | PInt Var
           | PPid Var
           | PProd ILPat ILPat
           | PSum  ILPat ILPat
             deriving (Ord, Eq, Read, Show, Typeable, Data)

data ILPred = ILBop Op ILExpr ILExpr                      
            | ILAnd ILPred ILPred
            | ILOr ILPred ILPred
            | ILNot ILPred 
            | ILPTrue
             deriving (Ord, Eq, Read, Show, Typeable, Data)

data Op = Eq | Lt | Le | Gt | Ge
             deriving (Ord, Eq, Read, Show, Typeable, Data)

data ILExpr = EUnit
            | EInt Int
            | EString
            | EPid Pid
            | EVar Var
            | ELeft ILExpr
            | ERight ILExpr
            | EPair ILExpr ILExpr
            | EPlus ILExpr ILExpr
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

            | SAssert { assertPred :: ILPred
                      , annot :: a
                      }

             -- x := p1 == p2;
            | SCompare { compareVar :: Var
                       , compareLhs :: Pid
                       , compareRhs :: Pid
                       , annot      :: a
                       }

            | SCase { caseVar   :: Var
                    , caseLPat   :: Var
                    , caseRPat   :: Var
                    , caseLeft  :: Stmt a
                    , caseRight :: Stmt a
                    , annot     :: a
                    }

            | SNonDet { nonDetBody :: [Stmt a]
                      , annot      :: a
                      }

            | SIncr { incrVar :: Var
                    , annot :: a

                    }
            | SDie { annot :: a }
            {- These do not appear in the source: -}
            | SNull { annot :: a }
            -- | SVarDecl Var a
            -- | STest Var a
         deriving (Ord, Eq, Read, Show, Functor, Foldable, Data, Typeable)

data SetBound = Known Set Int
              | Unknown Set Var
                deriving (Eq, Read, Show, Typeable)
type Process a = (Pid, Stmt a)
data Unfold = Conc Set Int deriving (Eq, Read, Show, Data, Typeable)

data Config a = Config {
    cTypes      :: MTypeEnv
  , cGlobals    :: [(Var, ILType)]
  , cGlobalSets :: [Set]
  , cSets       :: [SetBound]
  , cUnfold     :: [Unfold]
  , cProcs      :: [Process a]
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
    go (i@SCase {})    = [caseLPat i, caseRPat i]
    go _               = []
    goAbs :: Pid -> [Var]
    goAbs (PAbs v _) = [v]
    goAbs _          = []

unboundSets :: forall a. Data a => Stmt a -> [Set]
unboundSets s
  = allSetVars \\ boundSetVars
  where
    allSetVars = nub $ listify isSetVar s
    isSetVar (S _)       = True
    isSetVar (SV _)      = True
    isSetVar _           = False
    boundSetVars         = nub $ everything (++) (mkQ [] go) s
    go :: Data a => Stmt a -> [Set]
    go (SRecv (_, V x) _)= [S x] -- TODO
    go _                 = []

endLabels :: (Data a, Typeable a) => Stmt a -> [LVar]
endLabels = nub . listify (isPrefixOf "end" . unlv)

isBound :: Set -> [SetBound] -> Bool
isBound s = any p
  where p (Known s' _) = s == s'

boundAbs :: Config a -> Config a
boundAbs c@(Config {cProcs = ps, cSets = bs})
  = c { cUnfold = us }
  where
    us = [ Conc s n | (PAbs _ s, _) <- ps , Known s' n <- bs , s == s']

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
  traverse f (SCase v pl pr sl sr a)
    = mkCase <$> f a <*> traverse f sl <*> traverse f sr
    where
      mkCase a l r = SCase v pl pr l r a
  traverse f (SNonDet ss a)
    = flip SNonDet <$> f a <*> traverse (traverse f) ss
  traverse f (SIncr v a)
    = SIncr v <$> f a
  traverse f (SAssert p a)
    = SAssert p <$> f a
  traverse _ _
    = error "traverse undefined for non-source stmts"

joinMaps :: I.IntMap [a] -> I.IntMap [a] -> I.IntMap [a]
joinMaps = I.unionWith (++)

addNext :: Int -> [a] -> I.IntMap [a] -> I.IntMap [a]
addNext i is = I.alter (fmap (++is)) i

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
lastStmts (SCase _ _ _ sl sr _) = lastStmts sl ++ lastStmts sr
lastStmts s@(SDie a)        = [s]

buildCfg :: Stmt Int -> I.IntMap [Int]                              
buildCfg s = I.map (fmap annot) $ buildStmtCfg s
           
buildStmtCfg :: Stmt Int -> I.IntMap [Stmt Int]                              
buildStmtCfg = nextStmts 0

singleton :: Int -> Stmt Int -> I.IntMap [Stmt Int]
singleton i j
  | i == annot j = I.empty
  | otherwise    = I.fromList [(i, [j])]

nextStmts :: Int -> Stmt Int -> I.IntMap [Stmt Int]
nextStmts toMe s@(SNonDet ss i)
  = foldl' (\m -> joinMaps m . nextStmts i)
           (I.fromList [(toMe, [s])])
           ss

-- Blocks shouldn't be nested
nextStmts toMe s@SBlock { blkBody = ss }
  = singleton toMe s `joinMaps` snd nexts
  where
    nexts = foldl' go ([annot s], I.empty) ss
    -- go (ins, m) s = (annots s, foldl' go m `joinMaps` nextStmts ins s)
    go (ins, m) s = (annots s, foldl' joinMaps m (doMaps s <$> ins))
    doMaps s i    = nextStmts i s
    annots (SNonDet ts _) = annot <$> ts
    annots s              = [annot s]
                      
nextStmts toMe s@(SIter _ _ t i)
  = singleton toMe s `joinMaps`
    I.fromList [(annot j, [s]) | j <- lastStmts t]  `joinMaps`
    nextStmts i t

nextStmts toMe me@(SLoop v s i)
  = singleton toMe me `joinMaps`
    I.fromList [(j, [me]) | j <- js ] `joinMaps`
    nextStmts i s
  where
    js = [ j | SVar v' j <- listify (const True) s, v' == v]

nextStmts toMe me@(SChoose _ _ s i)
  = addNext toMe [me] $ nextStmts i s
nextStmts toMe me@(SCase _ _ _ sl sr i)
  = singleton toMe me `joinMaps` nextStmts i sl `joinMaps` nextStmts i sr
nextStmts toMe s
  = singleton toMe s

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
  pretty (GV x) = text x

instance Pretty Set where
  pretty (S x)   = text x
  pretty (SV x)  = text x
  pretty (SInts n) = brackets (int 1 <+> text ".." <+> int n)

instance Pretty Pid where
  pretty (PConc x)
    = text "pid@" <> int x
  pretty (PAbs v vs)
    = text "pid@" <> pretty vs <> brackets (pretty v)
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
  pretty (EInt i)  = int i
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
  pretty TString   = text "string"
  pretty TPid      = text "pid"
  pretty (TSum p1 p2)  = parens (pretty p1 <+> text "+" <+> pretty p2)
  pretty (TProd p1 p2) = parens (pretty p1 <+> text "*" <+> pretty p2)

instance Pretty Op where
  pretty Eq = text "="
  pretty Lt = text "<"
  pretty Le = text "≤"
  pretty Gt = text ">"
  pretty Ge = text "≥"

instance Pretty ILPred where
  pretty (ILBop o e1 e2) = parens (pretty e1 <+> pretty o <+> pretty e2)
  pretty (ILAnd p1 p2)   = parens (pretty p1 <+> text "&&" <+> pretty p2)
  pretty (ILOr p1 p2)    = parens (pretty p1 <+> text "||" <+> pretty p2)
  pretty (ILNot p)       = parens (text "~" <> pretty p)

instance Pretty (Stmt a) where
  pretty (SSkip _)
    = text "<skip>"

  pretty (SAssert e _)
    = text "assert" <+> pretty e

  pretty (SIncr v _)
    = pretty v <> text "++"

  pretty (SSend p (t,e) _)
    = text "send" <+> pretty p <+> parens (pretty e <+> text "::" <+> pretty t)

  pretty (SRecv (t,x) _)
    = text "recv" <+> parens (pretty x <+> text "::" <+> pretty t)

  pretty (SIter x xs s _)
    = text "for" <+> parens (int 0 <+> text "≤" <+> pretty x <+> langle <+> pretty xs) <+> lbrace $$
      (indent 2 $ pretty s) $$
      rbrace

  pretty (SVar (LV v) _)
    = text "goto" <+> pretty v

  pretty (SLoop (LV v) s _)
    = pretty v <> colon <+> parens (pretty s)

  pretty (SCase l pl pr sl sr _)
    = text "match" <+> pretty l <+> text "with" $$
      indent 2
        (align (vcat [text "| InL" <+> pretty pl <+> text "->" <+> pretty sl,
                     text "| InR" <+> pretty pr <+> text "->"  <+> pretty sr]))

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
    = vsep (map goGlob gs ++
            map goGlobS gsets ++
            map goB bs ++
            map go ps)
    where
      goGlob (v, t) = text "Global" <+> pretty v <+> text "::" <+> pretty t
      goGlobS s = text "Global" <+> pretty s
      goB (Known s n) = text "|" <> pretty s <> text "|" <+> equals <+> int n
      goB (Unknown s v) = text "|" <> pretty s <> text "|" <+> equals <+> pretty v
      go (pid, s) = text "Proc" <+> parens (pretty pid) <> colon <$$>
                    indent 2 (pretty s)

recvVars :: forall a. (Data a, Typeable a) => Stmt a -> [Var]
recvVars s
  = everything (++) (mkQ [] go) s
  where
    go :: Stmt a -> [Var]
    go (SRecv t _) = listify (const True) t
    go _           = []

patVars :: forall a. (Data a, Typeable a) => Stmt a -> [Var]
patVars s
  = nub $ everything (++) (mkQ [] go) s
  where
    go :: Stmt a -> [Var]
    go (SCase _ x y _ _ _) = [x, y]
    go _                   = []
