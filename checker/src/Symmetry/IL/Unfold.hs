{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Symmetry.IL.Unfold where

import           Prelude hiding (concatMap, mapM, foldl, concat)

import Symmetry.IL.AST
import Symmetry.IL.Subst

import           Data.Traversable
import           Data.Foldable
import           Data.Maybe
import           Control.Monad.State hiding (mapM)
import           Data.Typeable
import           Data.Generics
import           Data.List (nub, isPrefixOf, intersperse)
import qualified Data.Map.Strict as M

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
unfold1Loop _ _ s@(Iter _ (SInts _) _ _)
  = s
unfold1Loop _ bs s@(Iter _ r _ _)
  | r `elem` [ r' | Bounded r' _ <- bs ] = s
unfold1Loop ps _ (Iter v@(V x) set body i)
  = case abss of
      [] ->
        let lv = LV ("L" ++  x) in
        Loop lv (NonDet [ Block [body, Goto lv i] i
                          , Skip i
                          ] i) i
      [p] ->
        -- For each unfolded process, generate a block that
        -- 1. loops for a while on the abs proc
        -- 2. executes the body where an unfolded proc has been subbed
        --    for the abs proc
        -- 3. loops for a while on the abs proc
        Block (foldr (\(s,us) ss -> s:us:ss) [absLoop p lvout] inter) i
        where
          inter = zip (map (absLoop p . lvin) [0..]) ufStmts
      _ -> error "unexpected case in unfold1Loop"
  where
    lvin i = LV ("L" ++ x ++ "_in_" ++ show i)
    lvout = LV ("L" ++ x ++ "_out")
    absLoop p v = Loop v (NonDet [Block [doSub p, Goto v i] i
                                   ,Skip i] i) i-- Iter v set (doSub p) i
    doSub p = subst (sub1Pid v p) body
    abss = [ p | p@(PAbs _ set') <- ps, set' == set ]
    ufs = [ p | p@(PUnfold _ set' _) <- ps, set' == set ]
    ufStmts = map doSub ufs

unfold1Loop _ _ s = s
