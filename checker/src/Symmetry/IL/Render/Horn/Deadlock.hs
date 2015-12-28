module Symmetry.IL.Render.Horn.Deadlock where

import           Data.List
import           Data.Maybe
import           Data.Generics
import           Language.Haskell.Syntax

import           Symmetry.IL.AST as AST
import           Symmetry.IL.Render.Horn.Types

{- 
A configuration is deadlocked if 
  1. All processes are either blocked (i.e. at a receive) or stopped (PC = -1)
  2. At least one process is not done 
-}

-- Collect blocked states
-- /\_p (blocked-or-done p) /\ (\/_p' blocked p')

blockedLocsOfProc :: Process Int -> (Pid, [(ILType, Int)])
blockedLocsOfProc (p, s)
  = (p, everything (++) (mkQ [] go) s)
  where
    go :: Stmt Int -> [(ILType, Int)]
    go (SRecv (t,_) i) = [(t, i)]
    go _               = []


blockedLocs :: Config Int -> [(Pid, [(ILType, Int)])]
blockedLocs Config{ cProcs = ps }
  = blockedLocsOfProc <$> ps

procAtRecv :: TyMap -> Pid -> [(ILType, Int)] -> HsExp
procAtRecv _ p tis
  = ors [ pcEq p (toInteger i) | (_, i) <- tis ]

procDone :: Pid -> HsExp
procDone p
  = pcEq p (-1)

procBlocked :: TyMap -> Pid -> [(ILType, Int)] -> HsExp    
procBlocked m p@(PAbs v (S s)) tis
  = ands [ ors [ ands [ pcEq pk (toInteger i), blocked t ] | (t, i) <- tis ]
         , eq (counters tis) (dec (var $ prefix stateString s))
         ]
  where
    counters  = (foldl' add (readPCK (-1)) . (readPCK . snd <$>))
    readPCK i = readMap (pidPCCounterState p) (int i)
    blocked t = let tid = lookupTy t m in
                lte (readMyPtrw pk tid) (readMyPtrr pk tid)
    pk = PAbs (V (s ++ "_k")) (S s)

procBlocked m p tis
  = ors [ ands [pcEq p (toInteger i),  blocked t] | (t, i) <- tis ]
  where
    blocked t = let tid = lookupTy t m in
                lte (readMyPtrw p tid) (readMyPtrr p tid)

deadlockConfigs :: Config Int -> TyMap -> HsExp
deadlockConfigs c@Config { cProcs = ps } m
  = ors (badConfig <$> locs)
  where
    badConfig (p, tis) = ands [ procBlocked m p tis
                              , ands [ blockedOrDone q | q <- fst <$> ps, p /= q ]
                              ]
    locs            = blockedLocs c
    lkup p          = fromJust $ lookup p locs
    blockedOrDone p = ors [ procDone p, procBlocked m p (lkup p) ]

deadlockFree :: Config Int -> TyMap -> HsExp                      
deadlockFree c m
  = lneg $ deadlockConfigs c m
