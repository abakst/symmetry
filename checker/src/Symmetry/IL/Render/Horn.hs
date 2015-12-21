{-# Language TemplateHaskell #-}
{-# Language ScopedTypeVariables #-}
module Symmetry.IL.Render.Horn (render, runChecker) where

import           Language.Haskell.Syntax
import           Language.Haskell.Pretty
import           Data.Generics
import           Data.IntMap as M
import           Data.List   as L
import           Data.Maybe

import           Symmetry.IL.AST as AST
import           Symmetry.IL.Render.Horn.Spec
import           Symmetry.IL.Render.Horn.Deadlock
import           Symmetry.IL.Render.Horn.Decls
import           Symmetry.IL.Render.Horn.Types

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

type GuardedUpdate = (Maybe HsExp, [HsFieldUpdate])             

pcUpdateOfStmt :: IntMap [Int] -> Pid -> Stmt Int -> [GuardedUpdate]
pcUpdateOfStmt cfg p SIter {iterVar = (V v), iterSet = (S s) , annot = a}
  = case M.lookup a cfg of
      Just [i,j] -> [ (Just (lt ve se), updPC p a j),
                      (Just (lneg (lt ve se)), updPC p a i)
                    ]
      Just [i]   -> [ (Just (lt ve se), updPC p a i),
                      (Just (lneg (lt ve se)), updPC p a (-1))
                    ]
    where
      ve = readStateField p v
      se = readStateField p s
                    
pcUpdateOfStmt cfg p s
  = case M.lookup (annot s) cfg of
      Just [i] -> [(Nothing, updPC p (annot s) i)]
      _        -> [(Nothing, updPC p (annot s) (-1))]

-- stateUpdateOfStmt :: [Pid] -> TyMap -> Pid -> Stmt Int -> [HsFieldUpdate]                  
-- stateUpdateOfStmt dom m p (SSend (EPid q) (t,e) _)
--   = incPtrw tid p q ++
--     [ writeMsgBuf p q tid e
--     ]
--   where
--     tid = lookupTy t m
nextPC :: Pid -> Int -> Maybe [Int] -> [HsFieldUpdate]
nextPC p i (Just [j]) = updPC p i j
nextPC p i Nothing    = updPC p i (-1)

stateUpdateOfStmt :: [Pid] -> TyMap -> IntMap [Int] -> Pid -> Stmt Int -> [GuardedUpdate]
stateUpdateOfStmt dom m cfg p (SRecv (t,V x) i)
  = [(Nothing, nextPC p i next ++
               incPtrr tid p   ++ [updField p x (readMsgBuf p tid)])]
  where
    next = M.lookup i cfg
    tid = lookupTy t m

stateUpdateOfStmt dom m cfg p (SSend q (t,e) i)
  = case (M.lookup i cfg, q) of
      (n, EPid q) ->
        [ (Nothing, nextPC p i n ++ sendTo q) ]
      (n, EVar v) ->
        [ (Nothing, nextPC p i n ++ sendTo (PVar v)) ]
    where
      tid = lookupTy t m
      sendTo q = incPtrw tid p q ++
                 [writeMsgBuf p q tid e]

stateUpdateOfStmt dom m cfg p SIter{iterSet = (S s), iterVar = (V v), annot = a}
  = case M.lookup a cfg of
      Just [i,j] -> [ (Just (lte ve se)        , incr : updPC p a j)
                    , (Just (lneg $ lte ve se) , updPC p a i)
                    ]
      Just [i]   -> [ (Just (lte ve se)        , incr : updPC p a i)
                    , (Just (lneg $ lte ve se) , updPC p a (-1))
                    ]
    where
      incr = updField p v (inc (readStateField p v))
      ve = readStateField p v
      se = readStateField p s

stateUpdateOfStmt _ _ _ _ _ = []

{-
runStateOfStmt :: [Pid] -> TyMap -> IntMap [Int] -> Pid -> Stmt Int -> [HsGuardedRhs]
runStateOfStmt dom m cfg p s@SSend{sndPid = EVar (V v)}
  = [mkGuard guards (HsCase (readStateField p v) [HsAlt emptyLoc (pat p) (nextCall p) [] | p <- dom])]
  where
    pat p' = HsPApp (UnQual pidValConsName) [pidPatOfPid p']
    guards   = pcGuardOfStmt p s : stmtGuardsOfStmt m p s
    stUpdate p' = let s' = s { sndPid = EPid p' } in
                  let [(Nothing, pcu)] = pcUpdateOfStmt cfg p s' in
                  pcu ++ stateUpdateOfStmt dom m p s'
    nextCall p' = HsUnGuardedAlt $ HsVar (UnQual runStateName) $>$ updateState (stUpdate p')
                                                               $>$ HsVar (UnQual schedName)

runStateOfStmt dom m cfg p s =
  [mkGuard (guards g) (nextCall us) | (g, us) <- pcUpdateOfStmt cfg p s]
  where
    baseGuards  = pcGuardOfStmt p s : stmtGuardsOfStmt m p s
    guards g    = maybe baseGuards (\e -> e : baseGuards) g
    stUpdate    = stateUpdateOfStmt dom m p s
    nextCall us = HsVar (UnQual runStateName) $>$ updateState (us ++ stUpdate)
                                              $>$ HsVar (UnQual schedName)
-}

guardedCall gs rhs
  = HsGuardedRhs emptyLoc (ands gs) rhs

guardsOfStmt m p s@(SRecv (t,e) i)
  = [ pcGuardOfStmt p s
    , lt (pidReadTy p tid) (pidWriteTy p tid)
    ]
  where
    tid = lookupTy t m
guardsOfStmt _ p s
  = [pcGuardOfStmt p s]

-- stateUpdateOfStmt :: [Pid] -> TyMap -> IntMap [Int] -> Pid -> Stmt Int -> [GuardedUpdate]
-- stateUpdateOfStmt dom m cfg p s
--   = [(merge g g', us ++ us') | (g, us) <- pcUpds, (g', us') <- fieldUpds ] 
--   where
--     fieldUpds = fieldUpdateOfStmt cfg m p s

runStateOfStmt dom m cfg p s
  = [ guardedCall (guards g) (call us) | (g, us) <- stateUpdateOfStmt dom m cfg p s ]
  where
    guards (Just e) = e : guardsOfStmt m p s
    guards Nothing  = guardsOfStmt m p s
    call us         = HsVar (UnQual runStateName) $>$ updateState us
                                                  $>$ HsVar (UnQual schedName)

runStateOfProc :: [Pid] -> TyMap -> Process Int -> HsMatch
runStateOfProc dom m (p, s)
  = HsMatch emptyLoc runStateName argMatch (HsGuardedRhss (concatMap (runStateOfStmt dom m cfg p) stmts)) []
    where
      argMatch = [ HsPVar stateName, listHead (pidPatOfPid p) (HsPVar schedName)]
      cfg      = nextStmts s
      stmts    = listify (const True :: Stmt Int -> Bool) s

runStateOfConfig :: TyMap -> Config Int -> HsDecl
runStateOfConfig tyMap c@Config { cProcs = ps }
  = HsFunBind (transRel ++ [HsMatch emptyLoc runStateName args callAssert []])
  where
    transRel = runStateOfProc dom tyMap <$> ps
    args        = [HsPVar stateName, pids]
    callAssert  = HsUnGuardedRhs $ assert safetyE
    safetyE  = HsParen (deadlockFree c tyMap)
    dom    = fst <$> ps
    pids :: HsPat
    pids   = L.foldr go HsPWildCard dom
    go p rest = HsPInfixApp (pidPatOfPid p)
                            (Special HsCons)
                            rest

checkStateOfConfig :: Config Int -> [ HsDecl ]             
checkStateOfConfig c
  = [ HsTypeSig emptyLoc [checkName] (HsQualType [] unit_tycon)
    , HsFunBind [HsMatch emptyLoc checkName [] rhs []]
    ]
    where
      rhs = HsUnGuardedRhs (HsVar (UnQual runStateName)
                                    $>$ HsVar (UnQual initialName)
                                    $>$ HsParen (HsVar (UnQual initialSchedName) $>$
                                                 HsVar (UnQual initialName)))

initStateOfConfig :: Config Int -> [ HsDecl ]
initStateOfConfig c
  = [ HsTypeSig emptyLoc [initialName] (HsQualType [] (ty stateTyName))
    , HsPatBind emptyLoc (HsPVar initialName) def []
    ]
  where
    def = HsUnGuardedRhs (var "undefined")

initSchedOfConfig :: Config Int -> [ HsDecl ]
initSchedOfConfig c
  = [ HsTypeSig emptyLoc [initialSchedName] (HsQualType [] (ty stateTyName $->$ schedTy))
    , HsPatBind emptyLoc (HsPVar initialSchedName) def []
    ]
  where
    def = HsUnGuardedRhs (var "undefined")
                     
render :: Config a
       -> String
render c
  = unlines lhFile 
  where
    lhFile = [ prettyPrint modVerify
             , ""
             ] ++ spec
    modVerify = HsModule emptyLoc (Module "SymVerify") (Just []) [lhimport] decls
    decls     = initStateOfConfig c' ++
                initSchedOfConfig c' ++
                checkStateOfConfig c' ++
                runStateOfConfig tyMap c' :
                declsOfConfig c'
    c'        = c { cProcs = (freshStmtIds <$>) <$> cProcs c }
    lhimport  = HsImportDecl { importLoc = emptyLoc
                             , importModule = Module "Language.Haskell.Liquid.Prelude"
                             , importQualified = False
                             , importAs = Nothing
                             , importSpecs = Nothing
                             }

    types = nub $ listify (const True :: ILType -> Bool) (cProcs c')
    tyMap = zip types [0..] 

    spec = [ initSpecOfConfig tyMap c' ] ++ builtinSpec

runChecker :: Config a
           -> IO Bool
runChecker c = do putStrLn $ render c
                  return True
