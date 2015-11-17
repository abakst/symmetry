{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Symmetry.IL.AST where

import           Prelude hiding (concatMap, mapM, foldl, concat)
import           Data.Traversable
import           Data.Foldable
import           Data.Maybe
import           Control.Monad.State hiding (mapM)
import           Data.Typeable
import           Data.Generics
import           Data.List (nub, isPrefixOf, intersperse)
import qualified Data.Map.Strict as M
import Text.PrettyPrint.Leijen as P hiding ((<$>))

setSize :: Int
setSize = 1

infty :: Int
infty = 2

data Set = S String
         | SSetVar Var
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

unifyLabel (VL v) x
  = Just $ emptySubst { cLabSub = [(v, x)] }
unifyLabel x y
  | x == y    = Just emptySubst
  | otherwise = Nothing

unify :: MConstr -> MConstr -> Maybe Subst

unify (MCaseL x c) (MCaseL l c')
  = joinSubst <$> s <*> unify c c'
 where
   s = unifyLabel x l

unify (MCaseR x c) (MCaseR l c')
  = joinSubst <$> s <*> unify c c'
 where
   s = unifyLabel x l

unify (MTProd p1 p2) (MTProd p1' p2')
  = joinSubst <$> unify p1 p1' <*>  unify p2 p2'

unify a1@(MTApp{}) a2@MTApp{}
  | tycon a1 == tycon a2 &&
    length (tyargs a1) == length (tyargs a2)
  = if map (substPid sub) xs == ys then
      Just sub
    else
      Nothing
  where
    sub      = joinSubsts . catMaybes $ zipWith unifyPid xs ys
    (xs, ys) = (tyargs a1, tyargs a2)
unify _ _
  = Nothing

substLabel :: Subst -> Label -> Label
substLabel sub l@(VL v)
  = fromMaybe l $ lookup v (cLabSub sub)
substLabel _ l
  = l

unifyPid (PVar v) p = Just $ emptySubst { cPidSub = [(v, p)] }
unifyPid (PAbs v s) (PUnfold _ s' i)
  | s == s' = Just $ emptySubst { cIdxSub = [((v,s), i)] }
unifyPid p1 p2
  | p1 == p2  = Just emptySubst
  | otherwise = Nothing

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

            | SSend  { sndPid :: Pid
                     , sndMsg :: (TId, CId, MConstr)
                     , annot  :: a
                     }

            | SRecv  { rcvMsg :: (TId, CId, MConstr)
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
    cTypes  :: MTypeEnv
  , cSets   :: [SetBound]
  , cUnfold :: [Unfold]
  , cProcs  :: [Process a]
  } deriving (Eq, Read, Show, Typeable)

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
unfoldAbs c@(Config {cProcs = ps, cSets = bs})
  = c { cUnfold = us ++ cUnfold c }
  where
    us = [ Conc s 1 | (PAbs _ s, _) <- ps, not (isBound s bs) ]

isBound :: Set -> [SetBound] -> Bool
isBound s = any p
  where p (Bounded s' _) = s == s'

boundAbs :: Config a -> Config a
boundAbs c@(Config {cProcs = ps, cSets = bs})
  = c { cUnfold = us }
  where
    us = [ Conc s n | (PAbs _ s, _) <- ps , Bounded s' n <- bs , s == s']

instConstr :: [Pid] -> MConstr -> [MConstr]
instConstr dom c@(MTApp _ _)
  = map (`substCstr` c) . allSubs dom $ pvars c
instConstr dom (MCaseL _ c)
  = [MCaseL LL c' | c' <- instConstr dom c]
instConstr dom (MCaseR _ c)
  = [MCaseR RL c' | c' <- instConstr dom c]
instConstr dom (MTProd c1 c2)
  = [MTProd c1' c2' | c1' <- instConstr dom c1
                    , c2' <- instConstr dom c2]

instStmt  :: (Show a, Eq a)
          => [Pid] -> Stmt a -> Stmt a
instStmt dom s
  = SNonDet (nub [ s' | (_, s') <- instStmt' dom s ]) (annot s)

instStmt' :: Eq a => [Pid] -> Stmt a -> [(Subst, Stmt a)]
instStmt' dom (SNonDet (s:ss) a)
  = do (sub, s')             <- instStmt' dom s
       (sub', SNonDet ss' _) <- instStmt' dom (subst sub (SNonDet ss a))
       return (sub `joinSubst` sub', SNonDet (s' : ss') a)

instStmt' dom (SBlock (s:ss) a)
  = do (sub, s')    <- ts
       (sub', SBlock ss' _)  <- instStmt' dom (subst sub (SBlock ss a))
       return (sub `joinSubst` sub', SBlock (s' : ss') a)
  where
    ts = instStmt' dom s

instStmt' dom (SRecv (t,c,v) a)
  = [ (sub, SRecv (t, c, substCstr sub v) a)
    | sub <- psubs
    -- , coherent (substCstr sub v)
    ]
  where

    psubs     = allSubs dom (pvars v)
    -- lsubs     = foldl' go [emptySubst] (lvars v)
    -- subs      = [ s1 `joinSubst` s2 | s1 <- psubs, s2 <- lsubs ]
    -- go subs v = map (joinSubst (sub1Label v LL)) subs ++
    --             map (joinSubst (sub1Label v RL)) subs
    -- subs      = map (joinSubst lsub) psubs

  -- = [ (sub, SRecv (t,c, substCstr sub v) a) | sub <- allSubs dom (pvars v)
  --                                           , ]
instStmt' _ s = [(emptySubst, s)]

labSubCstr :: MConstr -> Subst
labSubCstr (MCaseL (VL x) c) = sub1Label x LL `joinSubst`
                               labSubCstr c
labSubCstr (MCaseL _ c)      = labSubCstr c
labSubCstr (MCaseR (VL x) c) = sub1Label x RL `joinSubst`
                               labSubCstr c
labSubCstr (MCaseR _ c)      =  labSubCstr c
labSubCstr (MTProd c1 c2) = labSubCstr c1 `joinSubst` labSubCstr c2
labSubCstr (MTApp {})     = emptySubst

allSubs :: [Pid] -> [Var] -> [Subst]
allSubs _ []
  = [emptySubst]
allSubs dom (x:xs)
  = [ su1 `joinSubst` surest | su1 <- subs x, surest <- allSubs dom xs ]
  where
    subs v  = [ emptySubst { cPidSub = [(v, p)] } | p <- dom ]

pvars :: MConstr -> [Var]
pvars (MTApp _ xs)   = [v | PVar v <- xs]
pvars (MCaseL _ c)   = pvars c
pvars (MCaseR _ c)   = pvars c
pvars (MTProd c1 c2) = nub (pvars c1 ++ pvars c2)

lvars :: MConstr -> [Var]
lvars (MTApp _ _)       = []
lvars (MCaseL (VL l) c) = l : lvars c
lvars (MCaseR (VL l) c) = l : lvars c
lvars (MCaseL _ c)      = lvars c
lvars (MCaseR _ c)      = lvars c
lvars (MTProd c1 c2)    = nub (lvars c1 ++ lvars c2)

instAbs :: (Show a, Eq a, Data a) => Config a -> Config a
instAbs c@(Config { cProcs = ps })
  = c { cProcs = map (inst1Abs dom) ps }
  where
    dom                          = map fst ps

inst1Abs :: (Show a, Data a, Eq a) => [Pid] -> Process a -> Process a
inst1Abs d (p@(PAbs _ _), s)
  = (p, flattenNonDet . instStmt d $ instLabels s)
  where
    -- All values of match vars:
    lsubs        = foldl' go [emptySubst] ls
    ls           = nub . concatMap lvars $ listify (const True) s
    go ss v      = [ s1`joinSubst`sub1Label v LL | s1 <- ss ] ++
                   [ s1`joinSubst`sub1Label v RL | s1 <- ss ]

    instLabels st =
      fromMaybe err $ filterCoherent (SNonDet (subLabels st) (annot st))

    err = error "inst1Abs: no labels are coherent"

    subLabels st = map (`subst` st) lsubs
inst1Abs _ p                 = p

flattenNonDet :: Eq a => Stmt a -> Stmt a
flattenNonDet (SNonDet ss a)
  = SNonDet (nub $ foldl' flatten [] ss) a
  where
    flatten ss' (SNonDet ss'' _)
      = ss' ++ map flattenNonDet ss''
    flatten ss' s'
      = ss' ++ [s']
flattenNonDet (SBlock ss a)
  = SBlock (map flattenNonDet ss) a
flattenNonDet s
  = s

coherent :: MConstr -> Bool
coherent (MTApp {})    = True
coherent (MCaseL LL c) = coherent c
coherent (MCaseR RL c) = coherent c
coherent (MTProd c1 c2)= coherent c1 && coherent c2
coherent _             = False

filterCoherent :: (Eq a) => Stmt a -> Maybe (Stmt a)
filterCoherent s@(SDie _)
  = Just s

filterCoherent (SNonDet ss a)
  = case mapMaybe filterCoherent ss of
      []   -> Nothing
      [s'] -> Just s'
      ss'  -> Just $ SNonDet (nub ss') a

filterCoherent s@(SBlock [] _)
  = Just s

filterCoherent (SBlock ss a)
  = if any isNothing ss' then
      Nothing
    else
      Just (SBlock (catMaybes ss') a)
  where
    ss' = map filterCoherent ss

filterCoherent s@(SSend _ (_,_,v) _)
  = if coherent v then Just s else Nothing

filterCoherent s@(SRecv (_,_,v) _)
  = if coherent v then Just s else Nothing

filterCoherent s@(SIter {})
  = do s' <- filterCoherent (iterBody s)
       return s { iterBody = s' }

filterCoherent s@(SLoop {})
  = do s' <- filterCoherent (loopBody s)
       return s { loopBody = s' }

filterCoherent s = Just s

unfoldLoops :: forall a.
               (Eq a, Data a, Typeable a)
            => Config a
            -> Config a
unfoldLoops c@Config { cProcs = ps, cSets = bs }
  = c { cProcs = everywhere (mkT go) ps }
  where
    pids = map fst ps
    go :: Stmt a -> Stmt a
    go = unfold1Loop pids bs

unfold1Loop :: (Eq a, Data a, Typeable a)
            => [Pid]
            -> [SetBound]
            -> Stmt a
            -> Stmt a
unfold1Loop _ _ s@(SIter _ (SInts _) _ _)
  = s
unfold1Loop _ bs s@(SIter _ r _ _)
  | r `elem` [ r' | Bounded r' _ <- bs ] = s
unfold1Loop ps _ (SIter v@(V x) set body i)
  = case abss of
      [] ->
        let lv = LV ("L" ++  x) in
        SLoop lv (SNonDet [ SBlock [body, SVar lv i] i
                          , SSkip i
                          ] i) i
      [p] ->
        -- For each unfolded process, generate a block that
        -- 1. loops for a while on the abs proc
        -- 2. executes the body where an unfolded proc has been subbed
        --    for the abs proc
        -- 3. loops for a while on the abs proc
        SBlock (foldr (\(s,us) ss -> s:us:ss) [absLoop p lvout] inter) i
        where
          inter = zip (map (absLoop p . lvin) [0..]) ufStmts
      _ -> error "unexpected case in unfold1Loop"
  where
    lvin i = LV ("L" ++ x ++ "_in_" ++ show i)
    lvout = LV ("L" ++ x ++ "_out")
    absLoop p v = SLoop v (SNonDet [SBlock [doSub p, SVar v i] i
                                   ,SSkip i] i) i-- SIter v set (doSub p) i
    doSub p = subst (sub1Pid v p) body
    abss = [ p | p@(PAbs _ set') <- ps, set' == set ]
    ufs = [ p | p@(PUnfold _ set' _) <- ps, set' == set ]
    ufStmts = map doSub ufs

unfold1Loop _ _ s = s

-- | Substitution of PidVars for Pids
type PidSubst = [(Var, Pid)]
type IdxSub = [((Var, Set), Int)]
type LabelSubst = [(Var, Label)]

data Subst = Subst { cPidSub :: PidSubst
                   , cLabSub :: LabelSubst
                   , cIdxSub :: IdxSub
                   } deriving (Eq, Show)

sub1Pid   v p = emptySubst { cPidSub = [(v, p)] }
sub1Label v l = emptySubst { cLabSub = [(v, l)] }

joinSubst c1 c2
  = Subst { cPidSub = cPidSub c1 ++ cPidSub c2
           , cLabSub = cLabSub c1 ++ cLabSub c2
           , cIdxSub = cIdxSub c1 ++ cIdxSub c2
           }

joinSubsts :: [Subst] -> Subst
joinSubsts
  = foldl' joinSubst emptySubst

emptySubst = Subst [] [] []

restrict :: Var -> Subst -> Subst
restrict x s
  = s { cPidSub = [(v, q) | (v, q) <- cPidSub s, v /= x]
      , cIdxSub = [(v, q) | (v, q) <- cIdxSub s, (fst v) /= x]
      }

subst :: Eq a => Subst -> Stmt a -> Stmt a
subst s (SNonDet ss a)
  = SNonDet (nub $ map (subst s) ss) a

subst s (SBlock ss a)
  = SBlock (map (subst s) ss) a

subst s (SSend p ms a)
  = SSend (substPid s p) (substMS s ms) a

subst s (SRecv ms a)
  = SRecv (substMS s ms) a

subst s (SIter v xs t a)
  = SIter v xs (subst s' t) a
  where s' = restrict v s

subst s (SLoop v t a)
  = SLoop v (subst s t) a

subst s (SCompare v p1 p2 a)
  = SCompare v (substPid s p1) (substPid s p2) a

subst s (SCase v l r a)
  = case lookup v (cLabSub s) of
      Just LL -> subst s l
      Just RL -> subst s r
      _       -> SCase v (subst s l) (subst s r) a

subst _ s = s

substCstr :: Subst -> MConstr -> MConstr
substCstr sub (MTApp tc as) = MTApp tc $ map (substPid sub) as
substCstr sub (MCaseL l c)  = MCaseL (substLabel sub l) $ substCstr sub c
substCstr sub (MCaseR l c)  = MCaseR (substLabel sub l) $ substCstr sub c
substCstr sub (MTProd c c') = MTProd (substCstr sub c) (substCstr sub c')

substMS :: Subst -> (TId, CId, MConstr) -> (TId, CId, MConstr)
substMS sub (ti,ci,m)
  = (ti, ci, substCstr sub m)

substPid :: Subst -> Pid -> Pid
substPid s p@(PVar v) = fromMaybe p $ lookup v (cPidSub s)
substPid sub p@(PAbs i s)
  = case lookup (i,s) (cIdxSub sub) of
      Nothing -> p
      Just n  -> PUnfold i s n
substPid _ p          = p

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
lastStmts (SIter _ _ s _)   = lastStmts s
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

freshIds :: Config a -> Config Int
freshIds (c @ Config { cProcs = ps })
  = c { cProcs = evalState (mapM (mapM freshId) ps) 1 }

instance Pretty Var where
  pretty (V x) = text x

instance Pretty Set where
  pretty (S x)        = text x
  pretty (SSetVar x)  = pretty x
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

instance Pretty (Stmt a) where
  pretty (SSkip _)
    = text "<skip>"

  pretty (SSend p m _)
    = text "send" <+> pretty p <+> prettyMsg m

  pretty (SRecv m _)
    = text "recv" <+> prettyMsg m

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
  pretty (Config {cProcs = ps, cSets = bs})
    = vcat (map goB bs) <$$> vcat (map go ps)
    where
      goB (Bounded s n) = text "|" <> pretty s <> text "|" <+> equals <+> int n
      go (pid, s) = text "Proc" <+> parens (pretty pid) <> colon <$$>
                    indent 2 (pretty s)
