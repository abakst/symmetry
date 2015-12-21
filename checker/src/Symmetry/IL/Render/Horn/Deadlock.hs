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
  = ors [ pcEq (pidCstrOfPid p) (toInteger i) | (_, i) <- tis ]

procDone :: Pid -> HsExp
procDone p
  = pcEq (pidCstrOfPid p) (-1)
    
procBlocked m p tis
  = ors [ ands [pcEq (pidCstrOfPid p) (toInteger i),  blocked t] | (t, i) <- tis ]
  where
    blocked t = let tid = lookupTy t m in
                lte (pidWriteTy p tid) (pidReadTy p tid)

deadlockFree :: Config Int -> TyMap -> HsExp
deadlockFree c m
  = lneg $ ands [allAtRecvOrDone, oneBlocked]
  where
    allAtRecvOrDone
      = ands [ ors [procAtRecv m p (lkup p), procDone p] | p <- ps]
    oneBlocked
      = ors [ procBlocked m p (lkup p) | p <- ps ]
    ps   = fst <$> cProcs c
    locs = blockedLocs c
    lkup p = fromJust $ lookup p locs
  --   absEnabled = ors [ absEnabled1 p ls | (p@(PAbs _ _), ls) <- locs ]
  --   absEnabled1 p@(PAbs _ (S s)) ls
  --     = lneg (eq (HsParen (sumLocs p (snd <$> ls))) (readGlobal s))
  --   sumLocs p ls = HsParen $ foldr (go p) (rdL p (-1)) ls
  --   go p l e = HsParen (var "+") $>$ rdL p l $>$ e
  --   rdL p l      = readMap (pidPCCounterState p) (int l)
