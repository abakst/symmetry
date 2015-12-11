{-# Language TemplateHaskell #-}
{-# Language ScopedTypeVariables #-}
module Symmetry.IL.Render.Horn (render, runChecker) where

import           Language.Haskell.Syntax
import           Language.Haskell.Pretty
import           Data.Generics
import           Data.Map as M
import           Data.List
import           Data.Maybe

import           Symmetry.IL.AST as AST
import           Symmetry.IL.Render.Horn.Deadlock
import           Symmetry.IL.Render.Horn.Decls
import           Symmetry.IL.Render.Horn.Types

{- schedule = [Pid] -}
{- 
   runState :: State -> Scheduler -> Quantified -> ()
-}

stmtGuardsOfStmt :: TyMap -> Pid -> Stmt Int -> [HsExp]
stmtGuardsOfStmt m p (SRecv (t,_) _)
  = [lt (pidReadTy p tid) (pidWriteTy p tid)]
    where
      tid = lookupTy t m
stmtGuardsOfStmt _ _ _
  = []
    
pcGuardOfStmt :: Pid -> Stmt Int -> HsExp
pcGuardOfStmt p s 
  = pcEq (pidCstrOfPid p) (toInteger (annot s))

mkGuard gs = HsGuardedRhs emptyLoc (ands gs)

pcUpdateOfStmt :: M.Map Int [Int] -> Pid -> Stmt Int -> HsFieldUpdate
pcUpdateOfStmt cfg p SIter {iterVar = (V v), iterSet = (S s) , annot = a}
  = case M.lookup a cfg of
      Just [i,j] -> updPC p (ifLte ve se (int j) (int i))
      Just [i]   -> updPC p (int i)
      _          -> updPC p (HsParen $ int (-1))
    where
      ve = readStateField p v
      se = readStateField p s
                    
pcUpdateOfStmt cfg p s
  = case M.lookup (annot s) cfg of
      Just [i] -> updPC p (int i)
      _        -> updPC p (HsParen $ int (-1))

stateUpdateOfStmt :: [Pid] -> TyMap -> Pid -> Stmt Int -> [HsFieldUpdate]                  
stateUpdateOfStmt dom m p (SSend (EPid q) (t,e) _)
  = [ incPtrw tid q
    , writeMsgBuf p q tid e
    ]
  where
    tid = lookupTy t m
stateUpdateOfStmt _ m p (SRecv (t,V x) _)
  = [ incPtrr tid p
    , updField p x (readMsgBuf p tid)
    ]
  where
    tid = lookupTy t m
stateUpdateOfStmt _ m p SIter{iterVar = (V v)}
  = [updField p v (inc (readStateField p v))]
stateUpdateOfStmt _ _ _ _ = []

runStateOfStmt :: [Pid] -> TyMap -> M.Map Int [Int] -> Pid -> Stmt Int -> HsGuardedRhs
runStateOfStmt dom m cfg p s@SSend{sndPid = EVar (V v)}
  = mkGuard guards (HsCase (readStateField p v) [HsAlt emptyLoc (pat p) (nextCall p) [] | p <- dom])
    
    -- [mkGuard (guards p') (nextCall p') | p' <- dom]
  where
    pat p' = HsPApp (UnQual pidValConsName) [pidPatOfPid p']
    guards   = pcGuardOfStmt p s : stmtGuardsOfStmt m p s
    stUpdate p' = let s' = s { sndPid = EPid p' } in
                  pcUpdateOfStmt cfg p s' : stateUpdateOfStmt dom m p s'
    nextCall p' = HsUnGuardedAlt $ HsVar (UnQual runStateName) $>$ updateState (stUpdate p')
                                                               $>$ HsVar (UnQual schedName)
runStateOfStmt dom m cfg p s =
  mkGuard guards nextCall
  where
    guards   = pcGuardOfStmt p s : stmtGuardsOfStmt m p s
    stUpdate = pcUpdateOfStmt cfg p s : stateUpdateOfStmt dom m p s
    nextCall = HsVar (UnQual runStateName) $>$ updateState stUpdate
                                           $>$ HsVar (UnQual schedName)

runStateOfProc :: [Pid] -> TyMap -> Process Int -> HsMatch
runStateOfProc dom m (p, s)
  = HsMatch emptyLoc runStateName argMatch (HsGuardedRhss (runStateOfStmt dom m cfg p <$> stmts)) []
    where
      argMatch = [ HsPVar stateName, listHead (pidPatOfPid p) (HsPVar schedName)]
      cfg      = nextStmts sIds
      stmts    = listify (const True :: Stmt Int -> Bool) sIds
      sIds     = freshStmtIds s

runStateOfConfig :: Config Int -> HsDecl
runStateOfConfig c@Config { cProcs = ps }
  = HsFunBind (transRel ++ [HsMatch emptyLoc runStateName args callAssert []])
  where
    transRel = runStateOfProc dom tyMap <$> ps
    args        = [HsPVar stateName, HsPWildCard]
    callAssert  = HsUnGuardedRhs $ assert safetyE
    safetyE  = HsParen (deadlockExpr c tyMap)
    dom   = fst <$> ps
    types = nub $ listify (const True :: ILType -> Bool) ps
    tyMap = zip types [0..] 

checkStateOfConfig :: Config Int -> HsDecl            
checkStateOfConfig c
  = HsFunBind [HsMatch emptyLoc checkName [] rhs []]
    where
      rhs = HsUnGuardedRhs (HsVar (UnQual runStateName) $>$ HsVar (UnQual initialName))

initStateOfConfig :: Config Int -> HsDecl
initStateOfConfig c
  = HsPatBind emptyLoc (HsPVar initialName) def []
  where
    def = HsUnGuardedRhs (HsRecConstr (UnQual stateTyName) [])
                     
render :: Config a
       -> String
render c
  = prettyPrint modVerify
  where
    modVerify = HsModule emptyLoc (Module "SymVerify") (Just []) [] decls
    decls     = initStateOfConfig c' :
                checkStateOfConfig c' :
                runStateOfConfig c'  :
                declsOfConfig c'
    runState  = runStateOfConfig c'
    c'        = freshIds c -- don't really need to do this...

runChecker :: Config a
           -> IO Bool
runChecker c = do putStrLn $ render c
                  return True
