{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Symmetry.IL.Inst where

import           Prelude hiding (concatMap, mapM, foldl, concat)

import Symmetry.IL.AST
import Symmetry.IL.Subst

import           Data.Foldable
import           Data.Maybe
import           Data.Generics
import           Data.List (nub)

instGlobals :: (Show a, Eq a, Data a) => Config a -> Config a
instGlobals c@(Config { cGlobals = gs, cGlobalSets = gsets, cProcs = ps })
  = undefined
  where
    sets = [ s | (PAbs _ s@(S _), _) <- ps ]

instAbs :: (Show a, Eq a, Data a) => Config a -> Config a
instAbs c@(Config { cProcs = ps })
  = c { cProcs = map (inst1Abs dom) ps }
  where
    dom = map fst ps

inst1Abs :: (Show a, Data a, Eq a) => [Pid] -> Process a -> Process a
inst1Abs d (p, s)
  = (p, flattenNonDet . instStmt d $ instLabels s)
  where
    -- All values of match vars:
    lsubs        = foldl' go [emptySubst] ls
    ls           = nub
                 . concatMap lvars $ listify (const True) s
    go ss v      = [ s1 `joinSubst` sub1Label v LL | s1 <- ss ] ++
                   [ s1 `joinSubst` sub1Label v RL | s1 <- ss ]

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
