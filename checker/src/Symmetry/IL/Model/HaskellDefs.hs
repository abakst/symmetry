{-# Language ParallelListComp #-}
module Symmetry.IL.Model.HaskellDefs where

import           Data.Char
import           Symmetry.IL.AST
import           Symmetry.IL.Model 
import           Language.Haskell.Exts.Build
import           Language.Haskell.Exts.Syntax hiding (Rule)

---------------------
-- Functions
---------------------
runState = "runState"

---------------------
-- Type Names
---------------------
valType, pidType, stateRecordCons :: String
pidType         = "Pid"
stateRecordCons = "State"
valType         = "Val"

schedType :: Type
schedType       = TyList (TyCon (UnQual (name pidType)))
schedTycon      = list_tycon

---------------------
-- Measures
---------------------
pidInj :: Pid -> String
pidInj p = prefix "is" (pid p)

valInj :: String -> String
valInj v = prefix "is" v            

---------------------
-- Pids
---------------------
pcCounter :: Pid -> String
pcCounter p = prefix (pc p) "k"

pidBound (PAbs _ (S s)) = s
              
pidConstructor :: Pid -> String
pidConstructor = (toUpper <$>) . pid

pidPattern :: Pid -> Pat
pidPattern p@(PConc _)
  = PApp (UnQual (name (pidConstructor p))) []
pidPattern p@(PAbs (GV v) _)
  = PParen (PApp (UnQual (name (pidConstructor p))) [pvar (name v)])
pidPattern _ = error "pidPattern: non conc or abs"
