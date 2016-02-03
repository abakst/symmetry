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
                          } 

data ConfigInfo a = CInfo { config     :: Config a
                          , stateVars  :: ConfigState
                          , tyMap      :: TyMap
                          , pids       :: [Pid]
                          , cfg        :: [(Pid, IntMap [Stmt Int])]
                          }

mkCState :: Config Int -> ConfigState 
mkCState c = CState { valVars    = vs
                    , intVars    = is
                    }
  where
    vs   = [ (p, v) | (p,s)  <- cProcs c, V v <- recvVars s ++ patVars s ]
    is   = [ (p, i) | (p, s) <- cProcs c, V i <- everything (++) (mkQ [] intVar) s ]

    intVar :: Stmt Int -> [Var]
    intVar (SIter { iterVar = i }) = [i]
    intVar (SLoop { loopVar = (LV i) }) = [V i]
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
