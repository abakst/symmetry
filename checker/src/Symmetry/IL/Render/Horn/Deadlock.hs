module Symmetry.IL.Render.Horn.Deadlock where

import           Data.List
import           Data.Maybe
import           Data.Generics
import           Language.Haskell.Syntax

import           Symmetry.IL.AST as AST
import           Symmetry.IL.Render.Horn.Config
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

procAtRecv :: ConfigInfo Int -> Pid -> [(ILType, Int)] -> HsExp
procAtRecv _ p tis
  = ors [ pcEq p (toInteger i) | (_, i) <- tis ]

procDone :: Pid -> HsExp
procDone p
  = pcEq p (-1)

procBlocked :: ConfigInfo Int -> Pid -> [(ILType, Int)] -> HsExp    
procBlocked ci p@(PAbs _ _) tis
  = ors [ ands [ pcEq p (toInteger i), blocked t ] | (t, i) <- tis ]
  where
    blocked t = let tid = lookupTy ci t in
                lte (readMyPtrw p tid) (readMyPtrr p tid)

procBlocked ci p tis
  = ors [ ands [pcEq p (toInteger i),  blocked t] | (t, i) <- tis ]
  where
    blocked t = let tid = lookupTy ci t in
                lte (readMyPtrw p tid) (readMyPtrr p tid)

deadlockFree :: ConfigInfo Int -> HsExp
deadlockFree ci@CInfo { config = Config { cProcs = ps } }
  = lneg $ ands [ assumption
                , ors (badConfig <$> locs)
                ]
  where
    badConfig (p, tis) = procBlocked ci p tis
    assumption      = ands [ blockedOrDone q | q <- fst <$> ps ]
    locs            = blockedLocs (config ci)
    lkup p          = fromJust $ lookup p locs
    blockedOrDone p@(PConc _)  = ors [ procDone p, procBlocked ci p (lkup p) ]
    blockedOrDone p@(PAbs _ _) = ands [ ors [ procDone p, procBlocked ci p (lkup p) ]
                                      , eq (counters p (lkup p))
                                           (dec (varn $ roleSizeName p))
                                      ]
    counters p  = (foldl' add (readPCK p (-1)) . (readPCK p . snd <$>))
    readPCK p i = readMap (pidPCCounterState p) (int i)
