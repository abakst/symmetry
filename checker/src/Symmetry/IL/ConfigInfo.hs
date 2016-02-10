{-# Language RecordWildCards #-}
module Symmetry.IL.ConfigInfo where

import Data.List as List
import Data.Maybe
import Data.IntMap.Strict as M
import Data.Generics

import Symmetry.IL.AST  

type TyMap = [(ILType, Integer)]                 

data ConfigState = CState { intVars     :: [(Pid, String)]
                          , valVars     :: [(Pid, String)]
                          , globVals    :: [String]
                          } 

data ConfigInfo a = CInfo { config     :: Config a
                          , stateVars  :: ConfigState
                          , tyMap      :: TyMap
                          , pids       :: [Pid]
                          , cfg        :: [(Pid, IntMap [Stmt Int])]
                          , isQC       :: Bool
                          }

mkCState :: Config Int -> ConfigState 
mkCState c = CState { valVars  = vs
                    , intVars  = is
                    , globVals = gs
                    }
  where
    vs   = [ (p, v) | (p,s)  <- cProcs c, V v <- recvVars s ++ patVars s ]
    is   = [ (p, i) | (p, s) <- cProcs c, V i <- everything (++) (mkQ [] intVar) s ]
    gs   = [ v | (V v, _) <- cGlobals c ]

    intVar :: Stmt Int -> [Var]
    intVar (SIter { iterVar = i }) = [i]
    -- intVar (SLoop { loopVar = (LV i) }) = [V i]
    intVar (SChoose { chooseVar = v }) = [v]
    intVar _                       = []

vars :: ConfigInfo a -> [String]                                     
vars CInfo { stateVars = CState {..} }
  = snd <$> intVars ++ valVars
  

cfgNext :: ConfigInfo Int -> Pid -> Int -> Maybe [Stmt Int]                                     
cfgNext ci p i
  = M.lookup i . fromJust $ List.lookup p (cfg ci)

mkCInfo :: Config Int -> ConfigInfo Int
mkCInfo c = CInfo { config    = c
                  , stateVars = mkCState c
                  , tyMap     = tyMap
                  , pids      = fst <$> cProcs c
                  , cfg       = mkCfg <$> cProcs c
                  , isQC      = False
                  }
  where
    mkCfg (p, s) = (p, buildStmtCfg s)
    types = nub $ everything (++) (mkQ [] go) (cProcs c)
    tyMap = zip types [0..] 
    go :: Stmt Int -> [ILType]
    go s@SRecv{} = [fst (rcvMsg s)]
    go s@SSend{} = [fst (sndMsg s)]
    go _         = []

lookupTy :: ConfigInfo a -> ILType -> Integer
lookupTy ci t = fromJust . List.lookup t $ tyMap ci

setBound :: ConfigInfo Int -> Set -> Maybe SetBound
setBound ci s
  | not (List.null known)   = Just $ head known
  | not (List.null unknown) = Just $ head unknown
  | otherwise               = Nothing
  where
    bs = cSets (config ci)
    known = [ k | k@(Known s' _) <- bs, s == s' ]
    unknown = [ u | u@(Unknown s' _) <- bs, s == s' ]

setBoundVars :: ConfigInfo a -> [Var]
setBoundVars ci
  = [ v | Unknown _ v <- cSets (config ci) ]
