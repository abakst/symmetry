module Symmetry.IL.Render.Horn.Deadlock where

import           Data.List
import           Data.Maybe
import           Data.Generics

import           Symmetry.IL.AST as AST
import           Symmetry.IL.Model
import           Symmetry.IL.Render.Horn.Config

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

procAtRecv :: ILModel e => ConfigInfo Int -> Pid -> [(ILType, Int)] -> e
procAtRecv ci p tis
  = ors [ readPC ci p `eq` int i | (_, i) <- tis ]

procDone :: ILModel e => ConfigInfo Int -> Pid -> e
procDone ci p
  = readPC ci p `eq` int (-1)

procBlocked :: ILModel e => ConfigInfo Int -> Pid -> [(ILType, Int)] -> e
procBlocked ci p@(PAbs _ _) tis
  = ors [ ands [ readPC ci p `eq` int i, blocked t ] | (t, i) <- tis ]
  where
    blocked t = lte (readPtrW ci p p t) (readPtrR ci p t)

procBlocked ci p tis
  = ors [ ands [readPC ci p `eq` (int i),  blocked t] | (t, i) <- tis ]
  where
    blocked t = lte (readPtrW ci p p t) (readPtrR ci p t)

deadlockFree :: ILModel e => ConfigInfo Int -> e
deadlockFree ci@CInfo { config = Config { cProcs = ps } }
  = lneg $ ands [ assumption
                , ors (badConfig <$> locs)
                ]
  where
    badConfig (p, tis) = procBlocked ci p tis
    assumption      = ands [ blockedOrDone q | q <- fst <$> ps ]
    locs            = blockedLocs (config ci)
    lkup p          = fromJust $ lookup p locs
    blockedOrDone p@(PConc _)  = ors [ procDone ci p, procBlocked ci p (lkup p) ]
    blockedOrDone p@(PAbs _ _) = ands [ ors [ procDone ci p, procBlocked ci p (lkup p) ]
                                      , eq (counters p (lkup p))
                                           (decr (readRoleBound ci p))
                                      ]
    counters p  = (foldl' add (readPCK p (-1)) . (readPCK p . snd <$>))
    readPCK p i = readPCCounter ci p (int i)
