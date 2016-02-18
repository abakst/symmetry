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
import           Text.Printf
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
         | VPtrR Type -- Special Variable (read ptr for type)
         | VPtrW Type -- Special Variable (read ptr for type)
         | VRef Pid String -- Reference another process's variable (for ghost state)
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

data Type = TUnit | TInt | TString | TPid | TProd Type Type | TSum Type Type
             deriving (Ord, Eq, Read, Show, Typeable, Data)

data Pat = PUnit
           | PInt Var
           | PPid Var
           | PProd Pat Pat
           | PSum  Pat Pat
             deriving (Ord, Eq, Read, Show, Typeable, Data)

data Pred = ILBop Op ILExpr ILExpr
          | ILAnd Pred Pred
          | ILOr Pred Pred
          | ILNot Pred
          | ILPTrue
            deriving (Ord, Eq, Read, Show, Typeable, Data)

data Op = Eq | Lt | Le | Gt | Ge
             deriving (Ord, Eq, Read, Show, Typeable, Data)

-- Predicates (Can we move to fixpoint refts? Or paramaterize over these?)
pTrue :: Pred
pTrue = ILPTrue

pFalse :: Pred
pFalse = ILBop Eq (EInt 0) (EInt 1)

pAnd :: Pred -> Pred -> Pred
pAnd p1 p2 = pSimplify (ILAnd p1 p2)

pSimplify :: Pred -> Pred        
pSimplify (ILAnd ILPTrue p) = pSimplify p
pSimplify (ILAnd p ILPTrue) = pSimplify p
pSimplify (ILOr ILPTrue _)  = pTrue
pSimplify (ILOr _ ILPTrue)  = pTrue
pSimplify (ILNot p)         = ILNot (pSimplify p)
pSimplify p                 = p


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

class Identable a where
  ident :: a -> Int

instance Identable Int where
  ident = id

instance Identable a => Identable (Stmt a) where
  ident = ident . annot

data PredAnnot a = PredAnnot { annotPred :: Pred, annotId :: a }
                 deriving (Ord, Eq, Read, Show, Data, Typeable)

instance Identable a => Identable (PredAnnot a) where
  ident = ident . annotId

data Stmt a = Skip { annot :: a }

            | Block { blkBody :: [Stmt a]
                    , annot :: a
                    }

            | Send  { sndPid :: ILExpr -- Pid
                    , sndMsg :: (Type, ILExpr)
                    , annot  :: a
                    }

            | Recv  { rcvMsg :: (Type, Var)
                    , annot  :: a
                    }

            | Iter { iterVar  :: Var
                   , iterSet  :: Set
                   , iterBody :: Stmt a
                   , annot    :: a
                   }

            {-used to create a loop with the given label-}
            | Loop { loopVar  :: LVar
                    , loopBody :: Stmt a
                    , annot    :: a
                    }

            | Choose { chooseVar :: Var
                      , chooseSet :: Set
                      , chooseBody :: Stmt a
                      , annot      :: a
                      }

            | Goto { varVar :: LVar
                   , annot  :: a
                   }

            | Assert { assertPred :: Pred
                      , annot :: a
                      }

             -- x := p1 == p2;
            | Compare { compareVar :: Var
                      , compareLhs :: Pid
                      , compareRhs :: Pid
                      , annot      :: a
                      }

            | Case { caseVar   :: Var
                   , caseLPat  :: Var
                   , caseRPat  :: Var
                   , caseLeft  :: Stmt a
                   , caseRight :: Stmt a
                   , annot     :: a
                   }

            | NonDet { nonDetBody :: [Stmt a]
                     , annot      :: a
                     }

            | Assign { assignLhs :: Var
                      , assignRhs :: ILExpr
                      , annot :: a
                      }

            | Die { annot :: a }
            {- These do not appear in the source: -}
            | Null { annot :: a }
            -- | GotoDecl Var a
            -- | STest Var a
         deriving (Ord, Eq, Read, Show, Functor, Foldable, Data, Typeable)

data SetBound = Known Set Int
              | Unknown Set Var
                deriving (Eq, Read, Show, Typeable)
type Process a = (Pid, Stmt a)
data Unfold = Conc Set Int deriving (Eq, Read, Show, Data, Typeable)

data Config a = Config {
    cTypes      :: MTypeEnv
  , cGlobals    :: [(Var, Type)]
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
    go (Recv (_,x) _) = [x]
    go (i@Iter {})    = [iterVar i]
    go (i@Choose {})  = [chooseVar i]
    go (i@Case {})    = [caseLPat i, caseRPat i]
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
    go (Recv (_, V x) _)= [S x] -- TODO
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

vars :: Pat -> [Var]
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
  traverse f (Skip a)
    = Skip <$> f a
  traverse f (Send p ms a)
    = Send p ms <$> f a
  traverse f (Recv ms a)
    = Recv ms <$> f a
  traverse f (Iter v s ss a)
    = flip (Iter v s) <$> f a <*> traverse f ss
  traverse f (Loop v ss a)
    = flip (Loop v) <$> f a <*> traverse f ss
  traverse f (Choose v s ss a)
    = flip (Choose v s) <$> f a <*> traverse f ss
  traverse f (Goto v a)
    = Goto v <$> f a
  traverse f (Compare v p1 p2 a)
    = Compare v p1 p2 <$> f a
  traverse f (Die a)
    = Die <$> f a
  traverse f (Block ss a)
    = flip Block <$> f a <*> traverse (traverse f) ss
  traverse f (Case v pl pr sl sr a)
    = mkCase <$> f a <*> traverse f sl <*> traverse f sr
    where
      mkCase a l r = Case v pl pr l r a
  traverse f (NonDet ss a)
    = flip NonDet <$> f a <*> traverse (traverse f) ss
  traverse f (Assign v e a)
    = Assign v e <$> f a
  traverse f (Assert p a)
    = Assert p <$> f a
  traverse _ _
    = error "traverse undefined for non-source stmts"

joinMaps :: I.IntMap [a] -> I.IntMap [a] -> I.IntMap [a]
joinMaps = I.unionWith (++)

addNext :: Int -> [a] -> I.IntMap [a] -> I.IntMap [a]
addNext i is = I.alter (fmap (++is)) i

stmt :: (TId, [(CId, MConstr)], Stmt a) -> Stmt a
stmt (_,_,s) = s

lastStmts :: Stmt a -> [Stmt a]
lastStmts s@(Skip _)           = [s]
lastStmts s@(Goto _ _)         = [s]
lastStmts s@(Compare _ _ _ _)  = [s]
lastStmts (Block ss _)         = [last ss]
lastStmts s@(Send _ _ _)       = [s]
lastStmts s@(Recv _ _)         = [s]
lastStmts (NonDet ss _)        = concatMap lastStmts ss
lastStmts (Choose _ _ s _)     = lastStmts s
lastStmts s@(Iter _ _ _ _)     = [s]
lastStmts (Loop _ s _)         = lastStmts s
lastStmts (Case _ _ _ sl sr _) = lastStmts sl ++ lastStmts sr
lastStmts s@(Die _)            = [s]
lastStmts s@Assert{}           = [s]
lastStmts _                    = error "lastStmts: TBD"

buildCfg :: (Data a, Identable a) => Stmt a -> I.IntMap [Int]
buildCfg s = I.map (fmap ident) $ buildStmtCfg s

buildStmtCfg :: (Data a, Identable a) => Stmt a -> I.IntMap [Stmt a]
buildStmtCfg = nextStmts 0

singleton :: Identable a => Int -> Stmt a -> I.IntMap [Stmt a]
singleton i j
  | i == ident j = I.empty
  | otherwise    = I.fromList [(i, [j])]

nextStmts :: (Data a, Identable a)
          => Int -> Stmt a -> I.IntMap [Stmt a]
nextStmts toMe s@(NonDet ss i)
  = foldl' (\m -> joinMaps m . nextStmts (ident i))
           (I.fromList [(toMe, [s])])
           ss

-- Blocks shouldn't be nested
nextStmts toMe s@Block { blkBody = ss }
  = singleton toMe s `joinMaps` snd nexts
  where
    nexts = foldl' go ([ident s], I.empty) ss
    go (ins, m) s' = (annots s', foldl' joinMaps m (doMaps s' <$> ins))
    doMaps s' i    = nextStmts (ident i) s'
    annots (NonDet ts _) = ident <$> ts
    annots s'             = [ident s']

nextStmts toMe s@(Iter _ _ t _)
  = singleton toMe s `joinMaps`
    I.fromList [(ident j, [s]) | j <- lastStmts t]  `joinMaps`
    nextStmts (ident s) t

nextStmts toMe me@(Loop v s _)
  = singleton toMe me `joinMaps`
    I.fromList [(j, [me]) | j <- js ] `joinMaps`
    nextStmts (ident s) s
  where
    js = [ j | Goto v' j <- listify (const True) s, v' == v]

nextStmts toMe me@(Choose _ _ s _)
  = addNext toMe [me] $ nextStmts (ident me) s
nextStmts toMe me@(Case _ _ _ sl sr _)
  = singleton toMe me `joinMaps`
    nextStmts (ident me) sl `joinMaps`
    nextStmts (ident me) sr
nextStmts toMe s
  = singleton toMe s

-- | Operations
freshId :: forall a b. (Int -> a -> b) -> Stmt a -> State Int (Stmt b)
freshId f s
  = mapM fr s
  where
    fr :: a -> State Int b
    fr a = do n <- get
              put (n + 1)
              return (f n a)

freshStmtIds :: (Int -> a -> b) -> Stmt a -> Stmt b
freshStmtIds f s = evalState (freshId f s) 0

freshIds :: Config a -> (Int -> a -> b) -> Config b
freshIds (c @ Config { cProcs = ps }) f
  = c { cProcs = evalState (mapM (mapM (freshId f)) ps) 1 }

instance Pretty Var where
  pretty (V x)     = text x
  pretty (GV x)    = text x
  pretty (VPtrR t) = text "Rd[" <> pretty t <> text "]"
  pretty (VPtrW t) = text "Wr[" <> pretty t <> text "]"
  pretty (VRef p v) = pretty v <> text "@" <> pretty p

instance Pretty Set where
  pretty (S x)   = text x
  pretty (SV x)  = text x
  pretty (SInts n) = brackets (int 1 <+> text ".." <+> int n)

instance Pretty Pid where
  pretty (PConc x)
    = text "pid" <> parens (int x)
  pretty (PAbs v vs)
    = text "pid" <> parens (pretty vs <> brackets (pretty v))
  pretty (PVar v)
    = text "pid" <> parens (pretty v)
  pretty (PUnfold _ s i)
    = text "pid" <> parens (pretty s <> brackets (int i))

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
  pretty EString   = text "<str>"
  pretty (EInt i)  = int i
  pretty (EVar v)  = pretty v
  pretty (EPid p)  = pretty p
  pretty (ELeft  e) = text "inl" <> parens (pretty e)
  pretty (ERight e) = text "inr" <> parens (pretty e)
  pretty (EPair e1 e2) = tupled [pretty e1, pretty e2]
  pretty (EPlus e1 e2) = pretty e1 <+> text "+" <+> pretty e2

instance Pretty Pat where
  pretty (PUnit )      = text "()"
  pretty (PInt v)      = text "int" <+> pretty v
  pretty (PPid v)      = text "pid" <+> pretty v
  pretty (PSum p1 p2)  = parens (pretty p1 <+> text "+" <+> pretty p2)
  pretty (PProd p1 p2) = parens (pretty p1 <+> text "*" <+> pretty p2)

instance Pretty Type where
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

instance Pretty Pred where
  pretty (ILBop o e1 e2) = parens (pretty e1 <+> pretty o <+> pretty e2)
  pretty (ILAnd p1 p2)   = parens (pretty p1 <+> text "&&" <+> pretty p2)
  pretty (ILOr p1 p2)    = parens (pretty p1 <+> text "||" <+> pretty p2)
  pretty (ILNot p)       = parens (text "~" <> pretty p)
  pretty (ILPTrue)       = text "T"

instance Pretty a => Pretty (PredAnnot a) where
  pretty PredAnnot { annotId = i, annotPred = ILPTrue } =
    text "/*" <+> pretty i <+> text "*/"
  pretty PredAnnot { annotId = i, annotPred = p } =
    text "/*" <+> pretty i <+> text "{"  <+> pretty p <> text "} */"

instance Pretty a => Pretty (Stmt a) where
  pretty (Skip a)
    = text "<skip>" <+> pretty a

  pretty (Assert e a)
    = text "assert" <+> pretty e <+> pretty a

  pretty (Assign v e a)
    = pretty v <+> text ":=" <+> pretty e <+> pretty a

  pretty (Send p (t,e) a)
    = text "send" <+> pretty p <+> parens (pretty e <+> text "::" <+> pretty t) <+> pretty a

  pretty (Recv (t,x) a)
    = text "recv" <+> parens (pretty x <+> text "::" <+> pretty t) <+> pretty a

  pretty (Iter x xs s a)
    = text "for" <+> parens (int 0 <+> text "≤"
                                   <+> pretty x
                                   <+> langle <+> text "|" <> pretty xs <> text "|")
                 <+> lbrace <+> pretty a $$ (indent 2 $ pretty s) $$ rbrace

  pretty (Goto (LV v) a)
    = text "goto" <+> pretty v <+> pretty a

  pretty (Loop (LV v) s a)
    = pretty v <> colon <+> parens (pretty s) <+> pretty a

  pretty (Case l pl pr sl sr a)
    = text "match" <+> pretty l <+> text "with"  <+> pretty a $$
      indent 2
        (align (vcat [text "| InL" <+> pretty pl <+> text "->" <+> pretty sl,
                     text "| InR" <+> pretty pr <+> text "->"  <+> pretty sr]))

  pretty (Choose v r s a)
    = text "select" <+> pretty v <+>
      text "from" <+> pretty r <+>
      text "in"  <+> pretty a $$ indent 2 (align (pretty s))

  pretty (Die a)
    = text "CRASH" <+> pretty a

  pretty (Block ss a)
    = braces (pretty a <> line <> indent 2 (vcat $ punctuate semi (map pretty ss)) <> line)

  pretty (Compare v p1 p2 _)
    = pretty v <+> colon <> equals <+> pretty p1 <+> equals <> equals <+> pretty p2

  pretty (NonDet ss a)
    = pretty ss <+> pretty a

  pretty (Null a)
    = text "<null>" <+> pretty a

prettyMsg :: (TId, CId, MConstr) -> Doc
prettyMsg (t, c, v)
  = text "T" <> int t <> text "@" <>
    text "C" <> int c <> parens (pretty v)

instance Pretty a => Pretty (Config a) where
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
    go (Recv t _) = listify (const True) t
    go _           = []

patVars :: forall a. (Data a, Typeable a) => Stmt a -> [Var]
patVars s
  = nub $ everything (++) (mkQ [] go) s
  where
    go :: Stmt a -> [Var]
    go (Case _ x y _ _ _) = [x, y]
    go _                   = []

------------------------
-- Remove explicit Assertions
------------------------
annotAsserts :: Data a => Config a -> Config (PredAnnot a)
annotAsserts c
  = c { cProcs = [ (p, squashAsserts s) | (p, s) <- cProcs c ] }

truePred :: a -> PredAnnot a
truePred a
  = PredAnnot { annotPred = ILPTrue
              , annotId   = a
              }

meetPred :: PredAnnot a -> PredAnnot a -> PredAnnot a    
meetPred p1 p2 = p2 { annotPred = pAnd (annotPred p1) (annotPred p2) }

squashAsserts :: forall a. Data a => Stmt a -> Stmt (PredAnnot a)    
squashAsserts s@Block { blkBody = [a@Assert{}] }
  = s { blkBody = [fmap truePred a]
      , annot   = truePred (annot s)
      }
squashAsserts s@Block { blkBody = (a@Assert{}):s1:body }
  = annotFirst ann $ squashAsserts s { blkBody = s1:body }
  where
    ann = PredAnnot { annotPred = assertPred a
                    , annotId   = annot a
                    }
squashAsserts s@Block { blkBody = b:body }
  = s { blkBody = b' `joinStmts` body'
      , annot   = truePred (annot s)
      }
    where
      b'        = fmap truePred b
      body'     = squashAsserts s { blkBody = body }
      joinStmts s1 s2@Block{} = s1 : blkBody s2
      joinStmts s1 s2         = [s1, s2]
squashAsserts s = fmap truePred s

annotFirst :: PredAnnot a -> Stmt (PredAnnot a) -> Stmt (PredAnnot a)
annotFirst a s@Block{ blkBody = b:body }
  = s { blkBody = b { annot = meetPred a (annot b) } : body }
annotFirst a s
  = s { annot = meetPred a (annot s) }
