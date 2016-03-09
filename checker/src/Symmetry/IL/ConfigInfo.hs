{-# Language RecordWildCards #-}
{-# Language ScopedTypeVariables #-}
module Symmetry.IL.ConfigInfo where

import Data.List as List
import Data.Maybe
import Data.IntMap.Strict as M
import Data.Generics

import Symmetry.IL.AST

type TyMap = [(Type, Integer)]

data ConfigState = CState { intVars     :: [(Pid, String)]
                          , valVars     :: [(Pid, String)]
                          , globVals    :: [String]
                          , globSets    :: [Set]
                          }

data ConfigInfo a = CInfo { config     :: Config a
                          , stateVars  :: ConfigState
                          , tyMap      :: TyMap
                          , pids       :: [Pid]
                          , cfg        :: [(Pid, IntMap [Stmt a])]
                          , isQC       :: Bool
                          , qcSamples  :: Int
                          }

mkCState :: forall a. Data a => Config a -> ConfigState
mkCState c = CState { valVars  = vs
                    , intVars  = is
                    , globVals = gs
                    , globSets = gsets
                    }
  where
    vs   = [ (p, v) | (p,s)  <- cProcs c, V v <- recvVars s ++ patVars s ]
    is   = nub $ [ (p, i) | (p, s) <- cProcs c, V i <- everything (++) (mkQ [] intVar) s ]
    gs   = [ v | (V v, _) <- cGlobals c ]
    gsets = cGlobalSets c

    intVar :: Stmt a -> [Var]
    intVar (Iter { iterVar = i }) = [i]
    intVar (Assign {assignLhs = i}) = [i]
    -- intVar (Loop { loopVar = (LV i) }) = [V i]
    intVar (Choose { chooseVar = v }) = [v]
    intVar _                       = []

vars :: ConfigInfo a -> [String]
vars CInfo { stateVars = CState {..} }
  = snd <$> intVars ++ valVars

cfgNext :: Identable a
        => ConfigInfo a -> Pid -> Int -> Maybe [Stmt a]
cfgNext ci p i
  = M.lookup i . fromJust $ List.lookup p (cfg ci)

mkCInfo :: forall a. (Data a, Identable a) => Config a -> ConfigInfo a
mkCInfo c = CInfo { config    = c
                  , stateVars = mkCState c
                  , tyMap     = tyMap
                  , pids      = fst <$> cProcs c
                  , cfg       = mkCfg <$> cProcs c
                  , isQC      = False
                  , qcSamples = 0
                  }
  where
    mkCfg (p, s) = (p, buildStmtCfg s)
    types = nub $ everything (++) (mkQ [] go) (cProcs c)
    tyMap = zip types [0..]
    go :: Stmt a -> [Type]
    go s@Recv{} = [fst (rcvMsg s)]
    go s@Send{} = [fst (sndMsg s)]
    go _         = []

lookupTy :: ConfigInfo a -> Type -> Integer
lookupTy ci t = fromJust . List.lookup t $ tyMap ci

setBound :: ConfigInfo a -> Set -> Maybe SetBound
setBound ci s
  | not (List.null known)   = Just $ head known
  | not (List.null unknown) = Just $ head unknown
  | otherwise               = Nothing
  where
    bs = cSetBounds (config ci)
    known = [ k | k@(Known s' _) <- bs, s == s' ]
    unknown = [ u | u@(Unknown s' _) <- bs, s == s' ]

allSets :: ConfigInfo a -> ([SetBound], [SetBound])
allSets ci 
  = ([ k | k@(Known _ _) <- sets], [ u | u@(Unknown _ _) <- sets])
  where
    sets = cSetBounds (config ci)

setBoundVars :: ConfigInfo a -> [Var]
setBoundVars ci
  = [ V s | set@(S s) <- cGlobalSets (config ci), isNothing (setBound ci set) ]

pidProc :: ConfigInfo a -> Pid -> Process a
pidProc ci (PAbs _ set)
  = head [ pr | pr@(PAbs _ set',_) <- cProcs (config ci), set == set' ]
pidProc ci p
  = fromJust $ List.lookup p (assocify <$> cProcs (config ci))
  where
    assocify x = (fst x, x)
