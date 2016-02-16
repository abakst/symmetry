{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Symmetry.IL.Subst where

import           Prelude hiding (concatMap, mapM, foldl, concat)

import Symmetry.IL.AST

import           Data.Traversable
import           Data.Foldable
import           Data.Maybe
import           Control.Monad.State hiding (mapM)
import           Data.Typeable
import           Data.Generics
import           Data.List (nub, isPrefixOf, intersperse)
import qualified Data.Map.Strict as M

subUnfoldIdx :: Pid -> Pid
subUnfoldIdx (PUnfold _ s i) = PUnfold (V (show i)) s i
subUnfoldIdx p = p

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
-- | Substitution of PidVars for Pids
type PidSubst   = [(Var, Pid)]
type IdxSub     = [((Var, Set), Int)]
type LabelSubst = [(Var, Label)]
type SetSubst   = [(Set, Set)]

data Subst = Subst { cPidSub :: PidSubst
                   , cLabSub :: LabelSubst
                   , cIdxSub :: IdxSub
                   , cSetSub :: SetSubst
                   } deriving (Eq, Show)

sub1Pid   v p = emptySubst { cPidSub = [(v, p)] }
sub1Label v l = emptySubst { cLabSub = [(v, l)] }

joinSubst :: Subst -> Subst -> Subst
joinSubst c1 c2
  = Subst { cPidSub = cPidSub c1 ++ cPidSub c2
           , cLabSub = cLabSub c1 ++ cLabSub c2
           , cIdxSub = cIdxSub c1 ++ cIdxSub c2
           , cSetSub = cSetSub c1 ++ cSetSub c2
           }

joinSubsts :: [Subst] -> Subst
joinSubsts
  = foldl' joinSubst emptySubst

emptySubst :: Subst
emptySubst = Subst [] [] [] []

restrict :: Var -> Subst -> Subst
restrict x s
  = s { cPidSub = [(v, q) | (v, q) <- cPidSub s, v /= x]
      , cIdxSub = [(v, q) | (v, q) <- cIdxSub s, (fst v) /= x]
      }

subst :: Eq a => Subst -> Stmt a -> Stmt a
subst s (NonDet ss a)
  = NonDet (nub $ map (subst s) ss) a

subst s (Block ss a)
  = Block (map (subst s) ss) a

subst s (Send p ms a)
  = Send (substPid s p) (substMS s ms) a

subst s (Recv ms a)
  = Recv (substMS s ms) a

subst s (Iter v xs t a)
  = Iter v (substSet s xs) (subst s' t) a
  where s' = restrict v s

subst s (Loop v t a)
  = Loop v (subst s t) a

subst s (Compare v p1 p2 a)
  = Compare v (substPid s p1) (substPid s p2) a

subst s (Case v l r a)
  = case lookup v (cLabSub s) of
      Just LL -> subst s l
      Just RL -> subst s r
      _       -> Case v (subst s l) (subst s r) a

subst _ s = s

substSet :: Subst -> Set -> Set
substSet s set@(SV v)
  = fromMaybe set $ lookup (SV v) (cSetSub s)
substSet _ s
  = s

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
substPid s (PAbs i v@(SV _))
  = case lookup (i, v') (cIdxSub s) of
      Nothing -> PAbs i v'
      Just n  -> PUnfold i v' n
    where v' = substSet s v
    
substPid sub p@(PAbs i s)
  = case lookup (i,s) (cIdxSub sub) of
      Nothing -> p
      Just n  -> PUnfold i s n
substPid _ p          = p
