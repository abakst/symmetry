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

procAtRecv :: TyMap -> Pid -> (ILType, Int) -> HsExp
procAtRecv m p (t, i)
  = ands [ pcEq (pidCstrOfPid p) (toInteger i)
         , lneg (lt (pidReadTy p tid) (pidWriteTy p tid))
         ]
    where
      tid = lookupTy t m

procDone :: Pid -> HsExp
procDone p
  = pcEq (pidCstrOfPid p) (-1)

    
procBlockedOrDone :: TyMap -> Pid -> [(ILType, Int)] -> HsExp
procBlockedOrDone m p recvs
  = ors (procDone p : (procAtRecv m p <$> recvs))
    
deadlockExpr :: Config Int -> TyMap -> HsExp
deadlockExpr c m
  = ands [ ands [procBlockedOrDone m p (lkup p) | p <- ps]
         , ors  [lneg (procDone p) | p <- ps]
         ]
  where
    ps   = fst <$> cProcs c
    locs = blockedLocs c
    lkup p = fromJust $ lookup p locs
