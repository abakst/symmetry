{-# Language TemplateHaskell #-}
{-# Language ScopedTypeVariables #-}
module Symmetry.IL.Render.Horn (render, runChecker) where

import           Language.Haskell.Syntax
import           Language.Haskell.Pretty
import           Data.Generics
import           Data.IntMap as M
import           Data.List   as L
import           Data.Maybe
import           Text.PrettyPrint.Leijen (pretty)

import           Symmetry.IL.AST as AST
import           Symmetry.IL.Render.Horn.Spec
import           Symmetry.IL.Render.Horn.Deadlock
import           Symmetry.IL.Render.Horn.Decls
import           Symmetry.IL.Render.Horn.Types

stmtGuardsOfStmt :: TyMap -> Pid -> Stmt Int -> [HsExp]
stmtGuardsOfStmt m p (SRecv (t,_) _)
  = [lt (readMyPtrr p tid) (readMyPtrw p tid)]
    where
      tid = lookupTy t m
stmtGuardsOfStmt _ _ _
  = []
    
pcGuardOfStmt :: Pid -> Stmt Int -> HsExp
pcGuardOfStmt p s 
  = pcEq p (toInteger (annot s))

mkGuard gs = HsGuardedRhs emptyLoc (ands gs)

type GuardedUpdate = ([HsExp], [HsFieldUpdate])             

updPCCounters :: Pid -> Int -> Int -> [GuardedUpdate]
updPCCounters p@(PAbs _ (S s)) pc pc'
  = [ ([grd], []), ([lneg grd], [pcku]) ]
  where
    grd = varn (idxNameOfPid p) `eq` (var (prefix stateString (s ++ "_k")))
    pcku = HsFieldUpdate (UnQual (pidLocCounterName p))
                         (writeMap (writeMap pcmap pce
                                               (dec (readMap pcmap pce)))
                                   pce'
                                   (inc (readMap pcmap pce')))
    pcmap = pidPCCounterState p                                   
    pce   = int pc
    pce'  = int pc'
updPCCounters _ _ _
  = []

sequenceUpdates :: [GuardedUpdate] -> [GuardedUpdate] -> [GuardedUpdate]            
sequenceUpdates gus []
  = gus
sequenceUpdates [] gus
  = gus            
sequenceUpdates gus gus'
  = [ (g ++ g', us ++ us') | (g, us) <- gus, (g', us') <- gus' ]

updatePC :: [HsExp] -> Pid -> Int -> Int -> [GuardedUpdate]    
updatePC g p pc pc'
  = sequenceUpdates [(g, updPC p pc pc')] (updPCCounters p pc pc')

nextPC :: [HsExp] -> Pid -> Int -> Maybe [Int] -> [GuardedUpdate]
nextPC g p i (Just [j])
  = updatePC g p i j
nextPC g p i Nothing
  = updatePC g p i (-1)
nextPC _ _ _ _
  = error "nextPC"

stateUpdateOfStmt :: [Pid] -> TyMap -> IntMap [Int] -> Pid -> Stmt Int -> [GuardedUpdate]
stateUpdateOfStmt _ m cfg p (SRecv (t,V x) i)
  = nextPC [] p i next `sequenceUpdates`
    [([], incPtrr tid p ++ [updField p x (readMsgBuf p tid)])]
  where
    next = M.lookup i cfg
    tid = lookupTy t m

stateUpdateOfStmt _ m cfg p (SSend q (t,e) i)
  = [([], sendTo pid)] `sequenceUpdates`
    nextPC [] p i j
    where
      (j, pid) = case (M.lookup i cfg, q) of
                  (j, EPid q) -> (j, q)
                  (j, EVar v) -> (j, PVar v)
      tid = lookupTy t m
      sendTo q = incPtrw tid p q ++
                 [writeMsgBuf p q tid e]

stateUpdateOfStmt _ _ cfg p SIter{iterSet = (S s), iterVar = (V v), annot = a}
  = [([], [incr])] `sequenceUpdates`
    (updatePC [lt ve se] p a i ++ updatePC [lte se ve] p a j)
    where
      (i, j) = case M.lookup a cfg of
                 Just [i,j] -> (j, i)
                 Just [i]   -> (i, -1)
      incr = updField p v (inc (readStateField p v))
      ve = readStateField p v
      se = readStateField p s

stateUpdateOfStmt _ _ cfg p SBlock {annot = a}
  = nextPC [] p a $ M.lookup a cfg

stateUpdateOfStmt _ _ _ _ s = error $ "TBD: " ++ show (pretty s)

guardedCall gs rhs
  = HsGuardedRhs emptyLoc (ands gs) rhs

guardsOfStmt m p s@(SRecv (t,e) i)
  = [ pcGuardOfStmt p s
    , lt (readMyPtrr p tid) (readMyPtrw p tid)
    ]
  where
    tid = lookupTy t m
guardsOfStmt _ p s
  = [pcGuardOfStmt p s]

runStateOfStmt :: [Pid] -> TyMap -> IntMap [Int] -> Pid -> Stmt Int -> [HsGuardedRhs]
runStateOfStmt dom m cfg p s@SSend { sndPid = EVar (V v) }
  = [ guardedCall (guards Nothing) caseSplit ]
  where
    guards (Just e) = e : guardsOfStmt m p s
    guards Nothing  = guardsOfStmt m p s
    caseSplit = HsCase (readStateField p v) (caseAlt <$> dom)
    caseAlt q = HsAlt emptyLoc (pat q) (call (updateState $ upds q)) []
    call    e = HsUnGuardedAlt (varn runStateName $>$ e $>$ varn schedName)
    pat     q = HsPApp (UnQual pidValConsName) [HsPParen (pidPatOfPid q)]
    upds    q = let [([], us)] = stateUpdateOfStmt dom m cfg p s { sndPid = EPid q }
                in us

runStateOfStmt dom m cfg p s
  = [ guardedCall (guards g) (call us) | (g, us) <- stateUpdateOfStmt dom m cfg p s ]
  where
    guards es = es ++ guardsOfStmt m p s
    call us   = HsVar (UnQual runStateName) $>$ updateState us
                                            $>$ HsVar (UnQual schedName)

runStateOfProc :: HsPat -> [Pid] -> TyMap -> Process Int -> HsMatch
runStateOfProc stateMatch dom m (p, s)
  = HsMatch emptyLoc runStateName argMatch (HsGuardedRhss (concatMap (runStateOfStmt dom m cfg p) stmts)) []
    where
      argMatch = [ stateMatch, listHead (pidPatOfPid p) (HsPVar schedName)]
      cfg      = nextStmts s
      stmts    = listify (const True :: Stmt Int -> Bool) s

runStateOfConfig :: TyMap -> Config Int -> HsDecl
runStateOfConfig tyMap c@Config { cProcs = ps }
  = HsFunBind (transRel ++ [HsMatch emptyLoc runStateName args callAssert []])
  where
    transRel = runStateOfProc statePattern dom tyMap <$> ps
    args        = [statePattern, pids]
    callAssert  = HsUnGuardedRhs $ assert safetyE
    safetyE  = HsParen (deadlockFree c tyMap)
    dom    = fst <$> ps
    pids :: HsPat
    pids   = L.foldr go HsPWildCard dom
    go p rest = HsPInfixApp (pidPatOfPid p)
                            (Special HsCons)
                            rest
    fields = stateFieldsOfConfig tyMap c
    statePattern = HsPAsPat stateName $
                            HsPRec (UnQual stateTyName)
                                   [HsPFieldPat (UnQual n) (HsPVar n) | ([n], _) <- fields]

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
                declsOfConfig tyMap c'
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
