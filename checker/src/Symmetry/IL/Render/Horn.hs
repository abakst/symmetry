{-# Language TemplateHaskell #-}
{-# Language ScopedTypeVariables #-}
{-# Language ViewPatterns #-}
module Symmetry.IL.Render.Horn (renderSimulator, renderQCFile) where

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
import           Symmetry.IL.Render.Horn.Config

stmtGuardsOfStmt :: ConfigInfo Int -> Pid -> Stmt Int -> [HsExp]
stmtGuardsOfStmt ci p (SRecv (t,_) _)
  = [lt (readMyPtrr p tid) (readMyPtrw p tid)]
    where
      tid = lookupTy ci t
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
    grd = varn (idxNameOfPid p) `eq` (varn (pidUnfoldName p))
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

nextPC :: [HsExp] -> Pid -> Int -> Maybe [Stmt Int] -> [GuardedUpdate]
nextPC g p i (Just [s])
  = updatePC g p i (annot s)
nextPC g p i Nothing
  = updatePC g p i (-1)
nextPC _ _ _ _
  = error "nextPC"

stateUpdateOfStmt :: ConfigInfo Int -> Pid -> Stmt Int -> [GuardedUpdate]
stateUpdateOfStmt ci p (SRecv (t,V x) i)
  = nextPC [] p i next `sequenceUpdates`
    [([], incPtrr tid p ++ [updField p x (readMsgBuf p tid)])]
  where
    next = cfgNext ci p i
    tid = lookupTy ci t

stateUpdateOfStmt ci p (SSend q (t,e) i)
  = [([], sendTo pid)] `sequenceUpdates`
    nextPC [] p i j
    where
      (j, pid) = case (cfgNext ci p i, q) of
                  (j, EPid q) -> (j, q)
                  (j, EVar v) -> (j, PVar v)
      tid = lookupTy ci t
      sendTo q = incPtrw tid p q ++
                 [writeMsgBuf p q tid e]

stateUpdateOfStmt _ p s@SChoose{chooseBody = b, chooseVar = (V v), annot = a}
  = updatePC [] p a (annot b) `sequenceUpdates` [([], u)] 
    where
      u = [updField p v nonDetRange]
      v' = name (v ++ "'")
      nonDetRange = HsLet [HsPatBind emptyLoc (HsPVar v') vDef []] assumeExp
      vDef = HsUnGuardedRhs $ HsParen (var nonDetString $>$ var schedString)
      assumeExp = HsParen $ case chooseSet s of
                              S s' -> var "liquidAssume"
                                         $>$ ands [ lte (int 0) (varn v')
                                                  , lt (varn v') (readStateField p s')
                                                  ]
                                         $>$ varn v'

stateUpdateOfStmt _ p SLoop{loopBody = s, annot = a}
  = updatePC [] p a (annot s)

stateUpdateOfStmt ci p SVar{annot = a}
  = nextPC [] p a $ cfgNext ci p a

stateUpdateOfStmt ci p SIncr{incrVar = (V v), annot = a}
  = [([], [incr])] `sequenceUpdates`
    (nextPC [] p a $ cfgNext ci p a)
  where
    incr = updField p v (inc (readStateField p v))

stateUpdateOfStmt ci p SIter{iterSet = s, iterVar = (V v), annot = a}
  = updatePC [lt ve se] p a i ++ updatePC [lte se ve] p a j
    where
      (i, j) = case (annot <$>) <$> cfgNext ci p a of
                 Just [i,j] -> (j, i)
                 Just [i]   -> (i, -1)
      ve = readStateField p v
      se = case s of
             S s'    -> readStateField p s'
             SInts n -> int n

stateUpdateOfStmt ci p SSkip{annot = a}
  = nextPC [] p a $ cfgNext ci p a

stateUpdateOfStmt ci p SBlock {annot = a}
  = nextPC [] p a $ cfgNext ci p a

stateUpdateOfStmt _ p SNonDet {nonDetBody = ss, annot = a}    
  = concat [ updatePC (guard i) p a i | i <- is ]
  where
    guard i = [eq (HsParen (varn nonDetName $>$ varn schedName)) (int i)]
    is      = annot <$> ss

stateUpdateOfStmt _ _ s = error $ "TBD: " ++ show (pretty s)

guardedCall gs rhs
  = HsGuardedRhs emptyLoc (ands gs) rhs

guardsOfStmt ci p s@(SRecv (t,e) i)
  = [ pcGuardOfStmt p s
    , lt (readMyPtrr p tid) (readMyPtrw p tid)
    ]
  where
    tid = lookupTy ci t
guardsOfStmt _ p s
  = [pcGuardOfStmt p s]

runStateOfStmt :: ConfigInfo Int -> Pid -> Stmt Int -> [HsGuardedRhs]
runStateOfStmt ci p s@SDie{}
  = [ guardedCall grd assertFalse ]
  where
    grd = guardsOfStmt ci p s
    assertFalse = assert (var "False")
runStateOfStmt ci p s@(SCase (V v) xl xr l r a)
  = [ guardedCall grd caseSplit ]
  where
    grd            = guardsOfStmt ci p s
    caseSplit      = HsCase (readStateField p v) cases
    call us        = varn runStateName $>$ updateState us $>$ varn schedName
    cases          = [ caseAlt (patLeft xl) xl l
                     , caseAlt (patRight xr) xr r]
    caseAlt p x s  = HsAlt emptyLoc p (guardedAlt (alt x s)) []
    alt (V v) s    = updatePC []  p a (annot s) `sequenceUpdates`
                     [([], [updField p v (var v)])]
    guardedAlt gups= HsGuardedAlts [HsGuardedAlt emptyLoc (ands g) (call us) | (g,us) <- gups]
    patLeft (V v)  = HsPApp (UnQual leftValConsName) [HsPVar (name v)]
    patRight (V v) = HsPApp (UnQual rightValConsName) [HsPVar (name v)]

runStateOfStmt ci p s@SSend { sndPid = EVar (V v) }
  = [ guardedCall grds caseSplit ]
  where
    grds      = guardsOfStmt ci p s
    caseSplit = HsCase (readStateField p v) (caseAlt <$> pids ci)
    caseAlt q = HsAlt emptyLoc (pat q) (guardedAlt (upds q)) [] 
    guardedAlt gups = HsGuardedAlts [HsGuardedAlt emptyLoc (ands g) (call us) | (g, us) <- gups ]
    call   us = varn runStateName $>$ updateState us $>$ varn schedName
    pat     q = HsPApp (UnQual pidValConsName) [HsPParen (pidPatOfPid q)]
    upds    q = stateUpdateOfStmt ci p s { sndPid = EPid q }

runStateOfStmt ci p s
  = [ guardedCall (guards g) (call us) | (g, us) <- stateUpdateOfStmt ci p s ]
  where
    guards es = es ++ guardsOfStmt ci p s
    call us   = HsVar (UnQual runStateName) $>$ updateState us
                                            $>$ HsVar (UnQual schedName)

runStateOfProc :: ConfigInfo Int -> HsPat -> Process Int -> HsMatch
runStateOfProc ci stateMatch (p, s)
  = HsMatch emptyLoc runStateName argMatch rhs []
    where
      rhs      = HsGuardedRhss (concatMap (runStateOfStmt ci p) stmts)
      m        = tyMap ci
      dom      = pids ci
      argMatch = [stateMatch, listHead (pidPatOfPid p) (HsPVar schedName)]
      stmts    = listify stmtFilter s
      stmtFilter :: Stmt Int -> Bool
      stmtFilter _        = True

runStateOfConfig :: ConfigInfo Int -> HsDecl
runStateOfConfig ci 
  = HsFunBind (transRel ++ [HsMatch emptyLoc runStateName args callAssert []]
                        ++ [makeItTotal])
  where
    ps       = cProcs (config ci)
    grds     = [ grd p | (p@(PAbs _ _), _) <- ps ]
    grd p    = varn (idxNameOfPid p) `eq` (varn (pidUnfoldName p))
    transRel = runStateOfProc ci statePattern <$> ps
    args        = [statePattern, pidsPat]
    callAssert  = HsGuardedRhss [guardedCall grds (assert safetyE)]
    safetyE  = HsParen (deadlockFree ci)
    pidsPat :: HsPat
    pidsPat   = L.foldr go HsPWildCard (pids ci)
    go p rest = HsPInfixApp (pidPatOfPid p)
                            (Special HsCons)
                            rest
    fields = stateFieldsOfConfig ci
    statePattern = HsPAsPat stateName $
                            HsPRec (UnQual stateTyName)
                                   [HsPFieldPat (UnQual n) (HsPVar n) | ([n], _) <- fields]
    makeItTotal = HsMatch emptyLoc
                          runStateName
                          [HsPWildCard, HsPWildCard]
                          (HsUnGuardedRhs (var "undefined"))
                          []

checkStateOfConfig :: ConfigInfo Int -> [ HsDecl ]             
checkStateOfConfig c
  = [ HsTypeSig emptyLoc [checkName] (HsQualType [] unit_tycon)
    , HsFunBind [HsMatch emptyLoc checkName [] rhs []]
    ]
    where
      rhs = HsUnGuardedRhs (HsVar (UnQual runStateName)
                                    $>$ HsVar (UnQual initialName)
                                    $>$ HsParen (HsVar (UnQual initialSchedName) $>$
                                                 HsVar (UnQual initialName)))

initStateOfConfig :: ConfigInfo Int -> [ HsDecl ]
initStateOfConfig c
  = [ HsTypeSig emptyLoc [initialName] (HsQualType [] (ty stateTyName))
    , HsPatBind emptyLoc (HsPVar initialName) def []
    ]
  where
    def = HsUnGuardedRhs (var "undefined")

initSchedOfConfig :: ConfigInfo Int -> [ HsDecl ]
initSchedOfConfig ci
  = [ HsTypeSig emptyLoc [initialSchedName]
                  (HsQualType [] (ty stateTyName $->$ schedTy))
    , HsPatBind emptyLoc (HsPVar initialSchedName) def []
    ]
  where
    def = HsUnGuardedRhs (var "undefined")
                     
renderSimulator :: Config a -> String
renderSimulator c
  = unlines lhFile 
  where
    lhFile = [ prettyPrint modVerify
             , ""
             ] ++ spec
    modVerify = HsModule emptyLoc (Module "SymVerify") Nothing imports decls
    decls     = initStateOfConfig cinfo ++
                initSchedOfConfig cinfo ++
                checkStateOfConfig cinfo ++
                runStateOfConfig cinfo :
                declsOfConfig cinfo
    imports   = mkImport <$> ["SymVector", "SymMap", "Language.Haskell.Liquid.Prelude"]
    mkImport m = HsImportDecl { importLoc = emptyLoc
                              , importQualified = False
                              , importAs = Nothing
                              , importModule = Module m
                              , importSpecs = Nothing
                              }
    cinfo   = mkCInfo c { cProcs = (freshStmtIds <$>) <$> cProcs c }

    spec = [ initSpecOfConfig cinfo ] ++ builtinSpec

renderQCFile :: Config a -> String
renderQCFile c
  = unlines lhFile
  where
    lhFile = [ prettyPrint modVerify
             , ""
             ] ++ spec
    modVerify = HsModule emptyLoc (Module "QC") (Just exports) imports decls
    exports   = []
    decls     = []
    imports   = mkImport <$> [ "SymVector"
                             , "SymMap"
                             , "SymVerify"
                             , "Language.Haskell.Liquid.Prelude"
                             , "Test.QuickCheck"]
    mkImport m = HsImportDecl { importLoc = emptyLoc
                              , importQualified = False
                              , importAs = Nothing
                              , importModule = Module m
                              , importSpecs = Nothing
                              }
    spec =  qcMainFunc ++ arbitraryDecls

qcMainFunc :: [String]
qcMainFunc = [ prettyPrint qcMainTypeDecl
             , prettyPrint qcMainFuncDecl ]

arbitraryDecls :: [String]
arbitraryDecls =  Prelude.map prettyPrint [ arbitraryValDecl ]
