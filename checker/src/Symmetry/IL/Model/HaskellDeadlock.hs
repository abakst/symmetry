{-# Language ScopedTypeVariables #-}
module Symmetry.IL.Model.HaskellDeadlock where

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

blockedLocsOfProc :: forall a. (Identable a, Data a)
                  => Process a -> (Pid, [(Type, Int)])
blockedLocsOfProc (p, s)
  = (p, everything (++) (mkQ [] go) s)
  where
    go :: Stmt a -> [(Type, Int)]
    go (Recv (t,_) i) = [(t, ident i)]
    go _               = []


blockedLocs :: (Data a, Identable a)
            => Config a -> [(Pid, [(Type, Int)])]
blockedLocs Config{ cProcs = ps }
  = blockedLocsOfProc <$> ps

procAtRecv :: ILModel e => ConfigInfo Int -> Pid -> [(Type, Int)] -> e
procAtRecv ci p tis
  = ors [ readPC ci (hackAbs p) `eq` int i | (_, i) <- tis ]

procDone :: ILModel e => ConfigInfo a -> Pid -> e
procDone ci p
  = readPC ci (hackAbs p) `eq` int (-1)

hackAbs :: Pid -> Pid
hackAbs p@(PAbs _ s) = PAbs (V (pidUnfold p)) s
hackAbs p = p

procBlocked :: (Identable a, ILModel e) => ConfigInfo a -> Pid -> [(Type, Int)] -> e
procBlocked ci p@(PAbs _ s) tis
  = ors [ ands [ readPC ci p' `eq` int i, blocked t ] | (t, i) <- tis ]
  where
    blocked t = lte (readPtrW ci p' p' t) (readPtrR ci p' t)
    p'        = PAbs (V (pidUnfold p)) s

procBlocked ci p tis
  = ors [ ands [readPC ci p `eq` (int i),  blocked t] | (t, i) <- tis ]
  where
    blocked t = lte (readPtrW ci p p t) (readPtrR ci p t)

deadlockFree :: (Data a, Identable a, ILModel e) => ConfigInfo a -> e
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
    readPCK p i = readMap (readPCCounter ci p) (int i)
