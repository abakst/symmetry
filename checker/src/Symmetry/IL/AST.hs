{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Symmetry.IL.AST where

import           Prelude hiding (concatMap, mapM, foldl, concat)
import           Data.Traversable
import           Data.Foldable
import           Data.Maybe
import           Control.Monad.State hiding (mapM)
import           Data.Typeable
import           Data.Generics
import           Data.List (nub, isPrefixOf)
import qualified Data.Map.Strict as M
import Text.PrettyPrint.Leijen as P hiding ((<$>))

setSize :: Int
setSize = infty
          
infty :: Int
infty = 2

data Set = S String
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

subUnfoldIdx :: Pid -> Pid
subUnfoldIdx (PUnfold _ s i) = PUnfold (V (show i)) s i
subUnfoldIdx p = p

data Label = LL | RL | VL Var
             deriving (Ord, Eq, Read, Show, Typeable, Data)

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

                      
lookupType m t
  = M.foldlWithKey go Nothing m
  where
    go Nothing i t' = if t == t' then Just i else Nothing
    go a       _ _  = a


-- a + (b * c) + d
-- if
--    :: c[t][from][me][1]?[x, A]
--    :: c[t][from][me][2]?[x, y, B, C]
--    :: c[t][from][me][3]?[x, y, D]
-- fi
-- mcasel ll a -- t[me 1]?[LL,A]
-- mcaser rl (mcase ll ll (prod b c))
-- mcase rl rr (mcase rl rr d)

type TId   = Int
type CId   = Int
type MType = M.Map CId MConstr

type MTypeEnv = M.Map TId MType

data Stmt a = SSkip a
            {- A Block should probably only be a sequence of
               SIters, SChoose ... -}
            | SBlock [Stmt a] a
            | SSend Pid [(TId, [(CId, MConstr)], Stmt a)] a
            | SRecv     [(TId, [(CId, MConstr)], Stmt a)] a
            | SIter Var Set (Stmt a) a
            | SLoop LVar (Stmt a) a         {-used to create a loop with the given label-}
            | SChoose Var Set (Stmt a) a
            | SVar LVar a
            | SCase Var (Stmt a) (Stmt a) a
            | SDie a
            {- These do not appear in the source: -}
            | SNull
            | SVarDecl Var a
            | STest Var a
            | SNonDet [Stmt a]
         deriving (Eq, Read, Show, Functor, Foldable, Data, Typeable)

-- (A a | B b | C (c + d))
--
-- recv (x : t1 + (t2 + t3))
-- x is
-- recv (t1 + t2)
-- -> SRecv(MTSum t1 t2)
-- -> if
--       :: t1?bloop
--       :: t2?blorp
--    fi

endLabels :: (Data a, Typeable a) => Stmt a -> [LVar]
endLabels = nub . listify (isPrefixOf "end" . unlv)

-- unifyWRRW (t1,p1,u1) (t2,p2,u2)
--   = do s <- unifyMType t1 t2
--        return ()

-- unifyMType (MTApp tc1 as) (MTApp tc2 as')
--   | tc1 == tc2  && length as == length as'
--     = foldM extendSub [] (zip as' as)
--   where
--     extendSub s (PVar v,p)
--       = maybe (return $ (v,p):s) (const Nothing) $ lookup v s

-- rwPairs :: Stmt Int -> [(MType, Pid, MType)]
-- rwPairs s
--   = everything (++) (mkQ [] rwPair) s

-- wrPairs :: Stmt Int -> [(MType, Pid, MType)]
-- wrPairs s
--   = everything (++) (mkQ [] wrPair) s

-- rwPair :: Stmt Int -> [(MType, Pid, MType)]
-- rwPair (SRecv mts _)
--   = [(m, p, m') | (m, (SSend p mts' _)) <- mts, (m',_) <- mts']
-- rwPair _
--   = []

-- wrPair :: Stmt Int -> [(MType, Pid, MType)]
-- wrPair (SSend p mts _)
--   = [(m, p, m') | (m, (SRecv mts' _)) <- mts, (m', _) <- mts']
-- wrPair _
--   = []

-- | Mark End
-- apLast :: (a -> a) -> [a] -> [a]
-- apLast f [x]    = [f x]
-- apLast f (x:xs) = x : apLast f xs

-- markEnd :: Stmt a -> Stmt a
-- markEnd (SBlock ss a)
--   = SBlock (apLast markEnd ss) a
-- markEnd (SSend p mts a)
--   = SSend p ((markEnd <$>) <$> mts) a
-- markEnd (SRecv mts a)
--   = SRecv ((markEnd <$>) <$> mts) a
-- markEnd (SIter v i s a)
--   = SIter v i (markEnd s) a
-- markEnd (SLoop

-- | Unfold
unfold :: Config a -> Config a
unfold c@(Config { cUnfold = us, cProcs = ps, cSets = bs })
  = c { cProcs = ps ++ ufprocs }
  where
    mkUnfold v s st i = (PUnfold v s i, st)
    ufprocs           = [ mkUnfold v s st (j + if isBound s bs then 0 else setSize)
                        | Conc s i <- us
                        , (PAbs v s', st) <- ps
                        , s == s'
                        , j <- [0..i-1]
                        ]

unfoldAbs :: Config a -> Config a
unfoldAbs c@(Config {cProcs = ps})
  = c { cUnfold = us }
  where
    us = [ Conc s 1 | (PAbs v s, _) <- ps ]
         
isBound :: Set -> [SetBound] -> Bool
isBound s = any p
  where p (Bounded s' _) = s == s'

boundAbs :: Int -> Config a -> Config a
boundAbs n c@(Config {cProcs = ps})
  = c { cUnfold = us, cSets = bs }
  where
    (us, bs) = unzip [ (Conc s n, Bounded s n) | (PAbs v s, _) <- ps ]

instStmt :: Eq a => [Pid] -> Stmt a -> Stmt a
-- Interesting Cases
instStmt dom (SRecv mts a)
  = SRecv   (concatMap (instMS dom) mts) a
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
instStmt dom (SCase v sl sr a)
  = SCase v (instStmt dom sl) (instStmt dom sr) a
instStmt _ (SVar v a)
  = SVar v a
instStmt _ (SDie a)
  = SDie a

instMS :: Eq a => [Pid] -> (TId, [(CId, MConstr)], Stmt a) -> [(TId, [(CId, MConstr)], Stmt a)]
instMS dom (t, cs, s)
  = foldl' doAllSubs i xs
  where
    i = [ (t,[(c,v)],s)  | (c, v) <- cs ]

    doAllSubs :: Eq a => [(TId, [(CId, MConstr)], Stmt a)] -> Var -> [(TId, [(CId, MConstr)], Stmt a)]
    doAllSubs ms x
      = nub $ concat [ map (substMS i) ms | i <- subs x ]

    xs = nub $ concat [ pvars c | (_, c) <- cs ]

    subs :: Var -> [Subst]
    subs x = [ [(x, q)] | q <- dom ]

pvars :: MConstr -> [Var]
pvars (MTApp _ xs)   = [v | PVar v <- xs]
pvars (MCaseL _ c)   = pvars c
pvars (MCaseR _ c)   = pvars c
pvars (MTProd c1 c2) = nub (pvars c1 ++ pvars c2)

instAbs :: Eq a => Config a -> Config a
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
subst s (SCase v l r a)  = SCase v (subst s l) (subst s r) a
subst _ stmt             = stmt

substCstr :: Subst -> MConstr -> MConstr
substCstr sub (MTApp tc as) = MTApp tc $ map (substPid sub) as
substCstr sub (MCaseL l c)  = MCaseL l $ substCstr sub c
substCstr sub (MCaseR l c)  = MCaseR l $ substCstr sub c
substCstr sub (MTProd c c') = MTProd (substCstr sub c) (substCstr sub c')

substMS :: Subst -> (TId, [(CId, MConstr)], Stmt a) -> (TId, [(CId, MConstr)], Stmt a)
substMS sub (ti,cs,s)
  = (ti, [ (ci, substCstr sub m) | (ci, m) <- cs ], subst sub s)

substPid :: Subst -> Pid -> Pid
substPid s p@(PVar v) = fromMaybe p $ lookup v s
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
annot (SDie a)          = a
annot (SLoop _ _ a)     = a
annot (SCase _ _ _ a)   = a
annot x                 = error ("annot: TBD " ++ show x)

instance Functor ((,,) a b) where
  fmap f (x,y,a) = (x,y,f a)

instance Foldable ((,,) a b) where
  foldMap f (_,_,y) = f y
  foldr f z (_,_,y) = f y z

instance Traversable ((,,) a b) where
  traverse f (x,y,a)= (,,) x y <$> f a

traversePat :: Applicative f => (a -> f b)
            -> (TId, [(CId, MConstr)], Stmt a)
            -> f (TId, [(CId, MConstr)], Stmt b)
traversePat f pat = traverse (traverse f) pat

-- | Typeclass tomfoolery
instance Traversable Stmt where
  traverse f (SSkip a)
    = SSkip <$> f a
  traverse f (SSend p ms a)
    = flip (SSend p) <$> f a <*> traverse (traversePat f) ms
  traverse f (SRecv ms a)
    = flip SRecv <$> f a <*> traverse (traversePat f) ms
  traverse f (SIter v s ss a)
    = flip (SIter v s) <$> f a <*> traverse f ss
  traverse f (SLoop v ss a)
    = flip (SLoop v) <$> f a <*> traverse f ss
  traverse f (SChoose v s ss a)
    = flip (SChoose v s) <$> f a <*> traverse f ss
  traverse f (SVar v a)
    = SVar v <$> f a
  traverse f (SDie a)
    = SDie <$> f a
  traverse f (SBlock ss a)
    = flip SBlock <$> f a <*> traverse (traverse f) ss
  traverse f (SCase v sl sr a)
    = mkCase <$> f a <*> traverse f sl <*> traverse f sr
    where
      mkCase a l r = SCase v l r a
  traverse _ _
    = error "traverse undefined for non-source stmts"

type Process a = (Pid, Stmt a)
data Unfold = Conc Set Int deriving (Eq, Read, Show, Data, Typeable)

joinMaps :: M.Map Int [a] -> M.Map Int [a] -> M.Map Int [a]
joinMaps = M.unionWith (++)

addNext :: Int -> [a] -> M.Map Int [a] -> M.Map Int [a]
addNext i is = M.alter (fmap (++is)) i

stmt :: (TId, [(CId, MConstr)], Stmt a) -> Stmt a
stmt (_,_,s) = s

lastStmts :: Stmt a -> [Stmt a]
lastStmts s@(SSkip _)       = [s]
lastStmts s@(SVar _ _)      = [s]
lastStmts (SBlock ss _)     = [last ss]
lastStmts (SSend _ ms _)    = concatMap (lastStmts . stmt) ms
lastStmts (SRecv ms _)      = concatMap (lastStmts . stmt) ms
lastStmts (SChoose _ _ s _) = lastStmts s
lastStmts (SIter _ _ s _)   = lastStmts s
lastStmts (SLoop _ s _)     = lastStmts s
lastStmts (SCase _ sl sr _) = lastStmts sl ++ lastStmts sr
lastStmts s@(SDie a)        = [s]

nextStmts :: Stmt Int -> M.Map Int [Int]
nextStmts (SSend _ ms i)
  = foldl (\m -> joinMaps m . nextStmts)
          (M.fromList [(i, map (annot . stmt) ms)])$ map stmt ms
nextStmts (SRecv ms i)
  = foldl (\m -> joinMaps m . nextStmts)
          (M.fromList [(i, map (annot . stmt) ms)])$ map stmt ms
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

data SetBound = Bounded Set Int
                deriving (Eq, Read, Show, Typeable)

data Config a = Config {
    cTypes  :: MTypeEnv
  , cSets   :: [SetBound]
  , cUnfold :: [Unfold]
  , cProcs  :: [Process a]
  } deriving (Eq, Read, Show, Typeable)

-- | Operations
freshId :: Stmt a -> State Int (Stmt Int)
freshId
  = mapM (const fr)
  where
    fr = do n <- get
            put (n + 1)
            return n

freshIds :: Config a -> Config Int
freshIds (c @ Config { cProcs = ps })
  = c { cProcs = evalState (mapM (mapM freshId) ps) 1 }

instance Pretty Var where
  pretty (V x) = text x

instance Pretty Set where
  pretty (S x) = text x

instance Pretty Pid where
  pretty (PConc x)
    = text "Pid@" <> int x
  pretty (PAbs v vs)
    = text "Pid@(" <> pretty v <> colon <> pretty vs <> text ")"
  pretty (PVar v)
    = pretty v
  pretty (PUnfold _ s i)
    = text "Pid@" <> pretty s <> brackets (int i)

x $$ y  = (x <> line <> y)

instance Pretty Label where
  pretty LL     = text "inl"
  pretty RL     = text "inr"
  pretty (VL x) = pretty x

instance Pretty MConstr where
  pretty (MTApp tc args) = text (untycon tc) <> pretty args
  pretty (MCaseL l t)    = pretty l <+> pretty t
  pretty (MCaseR l t)    = pretty l <+> pretty t
  pretty (MTProd t1 t2)  = pretty t1 <> text "*" <> pretty t2

instance Pretty (Stmt a) where
  pretty (SSkip _)
    = text "<skip>"

  pretty (SSend p tcms _)
    = text "send" <+> pretty p <+> align (doManyTCMS tcms)

  pretty (SRecv tcms _)    
    = text "recv" <+> align (doManyTCMS tcms)

  pretty (SIter x xs s a)
    = text "for" <+> parens (pretty x <+> colon <+> pretty xs) <+> lbrace $$
      (indent 2 $ pretty s) $$
      rbrace

  pretty (SVar (LV v) _)
    = text "goto" <+> pretty v

  pretty (SLoop (LV v) s _)
    = pretty v <> colon <+> parens (pretty s)

  pretty (SCase l sl sr a)
    = text "match" <+> pretty l <+> text "with" $$
      indent 2
        (align (vcat [text "| InL ->" <+> pretty sl,
                     text "| InR ->"  <+> pretty sr]))

  pretty (SDie _)
    = text "CRASH"

  pretty (SBlock ss _)
    = braces $ vcat $ punctuate semi (map pretty ss)

instance Pretty (Config a) where
  pretty (Config {cProcs = ps})
    = vcat $ map go ps
    where
      go (pid, s) = text "Proc" <+> parens (pretty pid) <> colon <$$>
                    indent 2 (pretty s)

doManyTCMS :: [(TId, [(CId, MConstr)], Stmt a)] -> Doc
doManyTCMS
  = align . braces . vcat . map doOneTCMS      

doOneTCMS :: (TId, [(CId, MConstr)], Stmt a) -> Doc
doOneTCMS (tid, cms, s)
  = text "T" <> int tid <> text "@" <>
    angles (align (vcat (punctuate punc (map doCMS cms))) <+>
            text "->" $$ align (pretty s))
  where
    punc = space <> text "+" <> space
    doCMS (ci, m)
      = text "C" <> int ci <> parens (pretty m) 
