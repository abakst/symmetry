{-# Language ScopedTypeVariables #-}
module Symmetry.IL.Deadlock where

import           Data.List
import           Data.Maybe
import           Data.Generics

import           Symmetry.IL.AST as AST
import           Symmetry.IL.Model
import           Symmetry.IL.ConfigInfo

{- 
A configuration is deadlocked if 
  1. All processes are either blocked (i.e. at a receive) or stopped (PC = -1)
  2. At least one process is not done 
-}

-- Collect blocked states
-- /\_p (blocked-or-done p) /\ (\/_p' blocked p')

blockedLocs :: (Data a, Identable a)
            => Config a -> [(Pid, [(Type, Int)])]
blockedLocs Config{ cProcs = ps }
  = blockedLocsOfProc <$> ps

procAtRecv :: ILModel e => ConfigInfo Int -> Pid -> [(Type, Int)] -> e
procAtRecv ci p tis
  = ors [ readPC ci (hackAbs p) (hackAbs p) `eq` int i | (_, i) <- tis ]

procDone :: ILModel e => ConfigInfo a -> Pid -> e
procDone ci p@(PAbs _ _)
  = readMap (readPCCounter ci p) (int (-1)) `eq` (readRoleBound ci p)
procDone ci p
  = readPC ci (hackAbs p) (hackAbs p) `eq` int (-1)

hackAbs :: Pid -> Pid
hackAbs p@(PAbs _ s) = PAbs (V (pidUnfold p)) s
hackAbs p = p

procBlocked :: (Identable a, ILModel e) => ConfigInfo a -> Pid -> [(Type, Int)] -> e
procBlocked ci p@(PAbs _ s) tis
  = ors [ ands [ readPC ci p' p' `eq` int i, blocked t ] | (t, i) <- tis ]
  where
    blocked t = lte (readPtrW ci p' p' t) (readPtrR ci p' p' t)
    p'        = PAbs (GV (pidUnfold p)) s

procBlocked ci p tis
  = ors [ ands [readPC ci p p `eq` (int i),  blocked t] | (t, i) <- tis ]
  where
    blocked t = lte (readPtrW ci p p t) (readPtrR ci p p t)

deadlockFree :: (Data a, Identable a, ILModel e) => ConfigInfo a -> e
deadlockFree ci@CInfo { config = Config { cProcs = ps } }
  = ors [ assumption
        , ands (procDone ci . fst <$> ps) -- ors (badConfig <$> locs)
        ]
  where
    badConfig (p, tis) = procBlocked ci p tis
    assumption      = ors [ notBlockedOrDone q | q <- fst <$> ps ]
    locs            = blockedLocs (config ci)
    lkup p          = fromJust $ lookup p locs
    notBlockedOrDone p@(PConc _)  = lneg (ors [ procDone ci p, procBlocked ci p (lkup p) ])
    -- blockedOrDone p@(PAbs _ _) = ands [ ors [ procDone ci p, procBlocked ci p (lkup p) ]
    --                                   , eq (counters p (lkup p))
    --                                        (decr (readRoleBound ci p))
    --                                   ]
    notBlockedOrDone p@(PAbs _ _) = (readPCK p (-1) `add` blockedCounter ci p p) `lt` (readRoleBound ci p)
    counters p  = (foldl' add (readPCK p (-1)) . (readPCK p . snd <$>))
    readPCK p i = readMap (readPCCounter ci p) (int i)
