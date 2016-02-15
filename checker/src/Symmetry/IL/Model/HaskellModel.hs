{-# Language ParallelListComp #-}
{-# Language TupleSections #-}
module Symmetry.IL.Model.HaskellModel where

import           Data.Char
import           Data.List
import           Data.Maybe
import           Data.Function
import           Text.Printf
import           Language.Haskell.Exts.SrcLoc
import           Language.Haskell.Exts.Syntax hiding (Rule, EVar)
import           Language.Haskell.Exts.Build
import           Language.Haskell.Exts.Pretty

import           Symmetry.IL.AST
import           Symmetry.IL.Model
import           Symmetry.IL.ConfigInfo
import           Symmetry.IL.Model.HaskellDefs
import           Symmetry.IL.Model.HaskellDeadlock
import           Symmetry.IL.Model.HaskellSpec (initSpecOfConfig)
  
---------------------------------
-- Wrapper type for Haskell code
---------------------------------
data HaskellModel = ExpM { unExp :: Exp }
                  | PatM { unPat :: Pat }
                  | StateUpM [(String, Exp)] [((Pid, ILType), Exp)]
                  | GuardedUpM Exp [(ILExpr, HaskellModel)]
                    deriving Show

---------------------
-- Convenience Functions                    
---------------------
vExp :: String -> Exp
vExp = var . name

opEq, opAnd, opOr, opPlus, opMinus, opLt, opLte, opGt, opGte :: QOp
opEq   = op (sym "==")
opAnd  = op (sym "&&")
opOr   = op (sym "||")
opPlus = op (sym "+")
opMinus= op (sym "-")
opLt   = op (sym "<")
opLte  = op (sym "<=")
opGt   = op (sym ">")
opGte  = op (sym ">=")

neg :: Exp
neg = vExp "not"

---------------------
-- Program Expressions
---------------------
getMap :: Exp -> Exp -> Exp
getMap m key
  = paren (app (app (vExp mapGetFn) m) key)

getVec :: Exp -> Exp -> Exp    
getVec vec key 
  = paren (app (app (vExp vecGetFn) key) vec)

getVec2D :: Exp -> Exp -> Exp -> Exp
getVec2D vec key1 key2 
  = paren (app (app (app (vExp vec2DGetFn) key1) key2) vec)

putMap :: Exp -> Exp -> Exp -> Exp
putMap m key val
  = paren (app (app (app (vExp mapPutFn) m) key) val)

putVec :: Exp -> Exp -> Exp -> Exp
putVec m key val
  = paren (app (app (app (vExp vecPutFn) key) val) m)

putVec2D :: Exp -> Exp -> Exp -> Exp -> Exp
putVec2D m key1 key2 val
  = paren (app (app (app (app (vExp vec2DPutFn) key1) key2) val) m)

stateUpdate :: [(String, Exp)] -> Exp
stateUpdate us
  = RecUpdate (vExp state) [FieldUpdate (UnQual (name f)) e | (f, e) <- us]
    
-- Implementations
hEq :: HaskellModel -> HaskellModel -> HaskellModel
hEq (ExpM e1) (ExpM e2)
  = ExpM $ paren (infixApp e1 opEq e2)

hLt :: HaskellModel -> HaskellModel -> HaskellModel
hLt (ExpM e1) (ExpM e2)
  = ExpM $ paren (infixApp e1 opLt e2)

hLte :: HaskellModel -> HaskellModel -> HaskellModel
hLte (ExpM e1) (ExpM e2)
  = ExpM $ paren (infixApp e1 opLte e2)

hAnd :: HaskellModel -> HaskellModel -> HaskellModel
hAnd (ExpM e1) (ExpM e2)
  = ExpM $ paren (infixApp e1 opAnd e2)

hOr :: HaskellModel -> HaskellModel -> HaskellModel
hOr (ExpM e1) (ExpM e2)
  = ExpM $ paren (infixApp e1 opOr e2)

hLNeg :: HaskellModel -> HaskellModel
hLNeg (ExpM b)
  = ExpM $ paren (app neg b)

hTrue, hFalse :: HaskellModel    
hTrue  = ExpM (vExp "True")
hFalse = ExpM (vExp "False")

hInt :: Int -> HaskellModel
hInt x
  = ExpM $ if x < 0 then paren (mkInt x) else mkInt x
  where
    mkInt = intE . toInteger 

hReadState :: ConfigInfo Int
           -> Pid
           -> String
           -> HaskellModel
hReadState _ (PConc _) f
  = ExpM $ vExp f
hReadState _ p f
  = ExpM $ getMap (vExp f) (vExp (pidIdx p))

hReadPC :: ConfigInfo Int
        -> Pid
        -> HaskellModel
hReadPC ci p
  = hReadState ci p (pc p)

hReadPCCounter :: ConfigInfo Int
               -> Pid
               -> HaskellModel
               -> HaskellModel
hReadPCCounter ci p (ExpM i)
  = ExpM $ getMap s i
  where
    s = vExp $ pcCounter p

hReadRoleBound :: ConfigInfo Int
               -> Pid
               -> HaskellModel
hReadRoleBound ci p
 = ExpM . vExp $ pidBound p

hIncr :: HaskellModel -> HaskellModel
hIncr (ExpM e)
  = ExpM $ infixApp e opPlus (intE 1)

hDecr :: HaskellModel -> HaskellModel
hDecr (ExpM e)
  = ExpM $ infixApp e opMinus (intE 1)

hAdd :: HaskellModel -> HaskellModel -> HaskellModel
hAdd (ExpM e1) (ExpM e2)
  = ExpM $ infixApp e1 opPlus e2

hSetFields :: ConfigInfo Int
           -> Pid
           -> [(String, HaskellModel)]
           -> HaskellModel
hSetFields ci (PConc _) ups
  = StateUpM [ (f, e) | (f, ExpM e) <- ups ] []
hSetFields ci p ups
  = StateUpM [ (f, putMap (vExp f) (vExp $ pidIdx p) e) | (f, ExpM e) <- ups ] []

hSetPC ci p e
  = hSetFields ci p [(pc p, e)]

con :: String -> Exp             
con = Con . UnQual . name

hExpr :: ConfigInfo Int -> Pid -> ILExpr -> HaskellModel
hExpr _ _ EUnit    = ExpM $ con unitCons    
hExpr _ _ EString  = ExpM $ con stringCons
hExpr _ _ (EInt i) = hInt i
hExpr _ _ (EPid q@(PConc _))
  = ExpM $ App (con pidCons) (vExp $ pidConstructor q)
hExpr ci p (EPid q@(PAbs (V v) _))
  = ExpM $ App (con pidCons) (App (vExp $ pidConstructor q) (unExp $ readState ci p v))
hExpr _ _ (EPid q@(PAbs _ _))
  = ExpM $ App (con pidCons) (App (vExp $ pidConstructor q) (vExp $ pidIdx q))
hExpr _ _ (EVar (GV v))
  = ExpM . vExp $ v
hExpr ci p (EVar (V v))
  = hReadState ci p v
hExpr ci p (ELeft e)
  = ExpM $ App (con leftCons) (unExp $ hExpr ci p e)
hExpr ci p (ERight e)
  = ExpM $ App (con rightCons) (unExp $ hExpr ci p e)
hExpr ci p (EPair e1 e2)
  = ExpM $ App (App (con pairCons) (unExp $ hExpr ci p e1))
               (unExp $ hExpr ci p e2)

hExpr ci p e
  = error (printf "hExpr: TBD(%s)" (show e))

hPred :: ConfigInfo Int -> Pid -> ILPred -> HaskellModel
hPred ci _ ILPTrue
  = ExpM $ vExp "True"
hPred ci p (ILNot b)
  = ExpM $ (paren (metaFunction "not" [unExp $ hPred ci p b]))
hPred ci p (ILAnd b1 b2)
  = ExpM $ InfixApp (unExp $ hPred ci p b1) opAnd (unExp $ hPred ci p b2)
hPred ci p (ILOr b1 b2)
  = ExpM $ InfixApp (unExp $ hPred ci p b1) opOr (unExp $ hPred ci p b2)
hPred ci p (ILBop o e1 e2)
  = ExpM $ paren (infixApp (unExp $ hExpr ci p e1)
                           (qop o)
                           (unExp $ hExpr ci p e2))
  where
    qop Eq = opEq
    qop Lt = opLt
    qop Le = opLte
    qop Gt = opGt
    qop Ge = opGte

hReadPtrR ci p t
  = hReadState ci p (ptrR ci p t)

hIncrPtrR ci p t
  = hSetFields ci p [(ptrR ci p t, hIncr ptrRExp)]
  where
    ptrRExp = hReadPtrR ci p t

hIncrPtrW ci p q t
  = hSetFields ci q [(ptrW ci q t, hIncr ptrWExp)]
  where
    ptrWExp = hReadPtrW ci p q t

hReadPtrW ci p q t
  = hReadState ci q (ptrW ci q t)

hPutMessage ci p q (e,t)
  = StateUpM [] [((q, t), e')]
  where
    ExpM e' = hExpr ci p e

hGetMessage ci p@PConc{} (V v, t)
  = hSetFields ci p [(v, ExpM $ getVec (vExp (buf ci p t)) e')]
  where
    ExpM e' = hReadPtrR ci p t

hGetMessage ci p@(PAbs (GV i) _) (V v, t)
  = hSetFields ci p [(v, ExpM $ getVec2D (vExp (buf ci p t)) (vExp i) e')]
  where
    ExpM e' = hReadPtrR ci p t

hMatchVal :: ConfigInfo Int
          -> Pid
          -> HaskellModel
          -> [(ILExpr, HaskellModel)]
          -> HaskellModel
hMatchVal ci p (ExpM f) cases
  | null cases = error "empty cases!"
  | otherwise  = GuardedUpM f cases
-- hMatchVal ci p f (EPid q) (Rule p' ms grd ups)
--   = Rule p' ((f, PatM $ pidPattern q) : ms) grd ups

-- hMatchVal ci p f (ELeft (EVar (V v))) (Rule p' ms grd ups)
--   = Rule p' ((f, PatM $ (PApp (UnQual (name leftCons)) [pvar (name v)])) : ms) grd ups

-- hMatchVal ci p f (ERight (EVar (V v))) (Rule p' ms grd ups)
--   = Rule p' ((f, PatM $ (PApp (UnQual (name rightCons)) [pvar (name v)])) : ms) grd ups

hNonDet :: ConfigInfo Int
        -> Pid
        -> HaskellModel
hNonDet _ _
  = ExpM $ metaFunction nondet [vExp sched]

hNonDetRange :: ConfigInfo Int
             -> Pid
             -> Set
             -> HaskellModel
hNonDetRange ci p (S s)
  = ExpM $ metaFunction nondetRange [intE 0, unExp $ readState ci p s]
hNonDetRange _ _ _
  = error "hNonDetRange (TBD)"

hRule :: ConfigInfo Int
      -> Pid
      -> HaskellModel
      -> Maybe (HaskellModel)
      -> HaskellModel
      -> Rule HaskellModel
hRule _ p g assert us
  = Rule p g assert us

hJoinUpdates _ _ (StateUpM us bufs) (StateUpM us' bufs')
  = StateUpM (us ++ us') (bufs ++ bufs')

instance ILModel HaskellModel where 
  int        = hInt
  add        = hAdd
  incr       = hIncr
  decr       = hDecr
  expr       = hExpr
  pred       = hPred
  lt         = hLt
  lte        = hLte
  eq         = hEq
  and        = hAnd
  or         = hOr
  lneg       = hLNeg
  true       = hTrue
  false      = hFalse
  readState  = hReadState
  readPtrR   = hReadPtrR
  readPtrW   = hReadPtrW
  readPC     = hReadPC
  readPCCounter = hReadPCCounter
  readRoleBound = hReadRoleBound
  nonDet = hNonDet
  nonDetRange = hNonDetRange

  joinUpdate = hJoinUpdates
  setPC      = hSetPC
  setState   = hSetFields
  incrPtrR   = hIncrPtrR
  incrPtrW   = hIncrPtrW
  putMessage = hPutMessage
  getMessage = hGetMessage

  rule       = hRule
  matchVal   = hMatchVal
  printModel = printHaskell
  printCheck = printQCFile


ilExpPat :: ILExpr -> Pat
ilExpPat (EPid q)
  = PApp (UnQual (name pidCons)) [pidPattern q]
ilExpPat (ELeft (EVar v))
  = PApp (UnQual (name leftCons)) [varPat v]
ilExpPat (ERight (EVar v))
  = PApp (UnQual (name rightCons)) [varPat v]
ilExpPat e
  = error (printf "ilExpPath TODO(%s)" (show e))

varPat :: Var -> Pat    
varPat (V v)  = pvar $ name v
varPat (GV v) = pvar $ name v

printRules ci rs dl = prettyPrint $ FunBind matches
  where
    matches = (mkMatch <$> perPid) ++ [ mkDlMatch ]
    mkMatch rules
      = Match noLoc (name runState) (pat [rulesPid rules]) Nothing (mkGuardedRhss rules) Nothing 
    mkGuardedRhss rules
      = GuardedRhss [ mkRhs p grd a up | Rule p (ExpM grd) a up <- rules ]
    mkRhs p grd a (GuardedUpM f cases)
      = GuardedRhs noLoc [Qualifier grd] (Case f (mkAlt p a <$> cases))
    mkRhs p grd a (StateUpM fups bufups)
      = GuardedRhs noLoc [Qualifier grd] (mkCall p a fups bufups)
    -- mkRhs p ms grd fups bufups
    --   = GuardedRhs noLoc [Qualifier grd] (mkCall p fups bufups)
    mkAlt p a (ile, StateUpM fups bufups)
      = Alt noLoc (ilExpPat ile) (UnGuardedRhs (mkCall p a fups bufups)) Nothing
    -- mkCase [(f, PatM p)] e
    --   = Case (vExp f) [Alt noLoc p (UnGuardedRhs e) Nothing]
    mkRecUp p fups
      = RecUpdate (vExp state) [mkFieldUp p f e | (f,e) <- fups]
    mkFieldUp p f e
      = FieldUpdate (UnQual (name f)) e
    mkCall p (Just (ExpM e)) fups bufups
      = mkAssert e (paren (mkCall p Nothing fups bufups))
    mkCall p Nothing fups bufups
      = metaFunction runState
          (mkRecUp p fups : mkBufUps bufups ++ [vExp sched]) 
    mkBufUps bufups
      = [ findUp p t bufups | p <- pids ci, t <- fst <$> tyMap ci]

    rulesPid rules = let Rule p _ _ _ = head rules in p
    pidRule (Rule p _ _ _) = p
    eqPid  = (==) `on` pidRule
    perPid = groupBy eqPid $ sortBy (compare `on` pidRule) rs

    pat ps = [ PAsPat (name state) (PRec (UnQual (name stateRecordCons)) [PFieldWildcard]) ] ++
             [ pvar (name (buf ci q t)) | q <- pids ci, t <- fst <$> tyMap ci ] ++
             [ mkSchedPat ps ]

    mkSchedPat ps = foldr (\q rest -> PInfixApp (pidPattern q) list_cons_name rest) schedPVar ps
    schedPVar  = pvar (name sched)

    mkDlMatch  = Match noLoc (name runState) dlpat Nothing dlRhs Nothing
    dlRhs      = UnGuardedRhs (mkAssert dl unit_con)
    dlpat      = pat (pids ci)

    findUp p t bufups
      = maybe (vExp $ buf ci p t) (\(p, e) -> updateBuf ci p t e) $ findUpdate p t bufups

mkAssert e k
  = infixApp (metaFunction "liquidAssert" [e]) (op . sym $ "$") k

updateBuf :: ConfigInfo Int -> Pid -> ILType -> Exp -> Exp
updateBuf ci p@(PAbs _ _) t e
  = putVec2D v i j e 
    where
      v = vExp $ buf ci p t
      i = vExp $ pidIdx p
      j = getMap (vExp $ ptrW ci p t) (vExp $ pidIdx p)
updateBuf ci p t e
  = putVec v i e
  where
    v = vExp $ buf ci p t
    i = vExp $ ptrW ci p t
          

findUpdate :: Pid -> ILType -> [((Pid, ILType), Exp)] -> Maybe (Pid, Exp)
findUpdate (PAbs _ (S s)) t bufups
  = case [ (p, e) | ((p@(PAbs _ (S s')), t'), e) <- bufups, s == s', t == t' ] of
      []  -> Nothing
      x:_ -> Just x
findUpdate p t bufups
  = (p,) <$> lookup (p, t) bufups

undef = "undefined"                               
undefinedExp = vExp undef

initialState :: ConfigInfo Int -> [Decl]
initialState _
  = [ TypeSig noLoc [name initState] (TyCon (UnQual (name stateRecordCons)))
    , nameBind noLoc (name initState) undefinedExp
    ]

initialSched :: ConfigInfo Int -> [Decl]
initialSched _
  = [ TypeSig noLoc [name initSched] fnType
    , simpleFun noLoc (name initSched) (name state) undefinedExp
    ]
  where
    fnType = TyFun (TyCon (UnQual (name stateRecordCons)))
                   schedType

    -- -- Match noLoc (name runState) (pat [rulesPid rules]) Nothing (mkGuardedRhss rules) Nothing
    -- totalRunState = Match noLoc (name runState)
    --                       (pat [rulesPid rules])
    --                       Nothing
    --                       (UnGuardedRhs (Con $ Special UnitCon))
    --                       Nothing

totalCall :: ConfigInfo Int -> Decl
totalCall ci =
  FunBind [Match noLoc (name runState) args Nothing rhs Nothing]
    where
      bufs = [ wildcard | _ <- pids ci, _ <- tyMap ci ]
      args = wildcard : bufs ++ [wildcard]
      rhs  = UnGuardedRhs $ Con $ Special $ UnitCon

initialCall :: ConfigInfo Int -> Decl
initialCall ci =
  nameBind noLoc (name "check") call
    where
      call = metaFunction runState (vExp initState : bufs ++ [initSchedCall])
      bufs = [ emptyVec p | p <- pids ci, _ <- tyMap ci ]
      emptyVec p = vExp $ if isAbs p then "emptyVec2D" else "emptyVec"
      initSchedCall = metaFunction initSched [vExp initState]
          
printHaskell :: ConfigInfo Int -> [Rule HaskellModel] -> String
printHaskell ci rs = unlines [ header
                             , ""
                             , body
                             ]
  where
    header = unlines [ "{-# Language RecordWildCards #-}"
                     , "module SymVerify where"
                     , "import SymVector"
                     , "import SymMap"
                     , "import SymBoilerPlate"
                     , "import Language.Haskell.Liquid.Prelude"
                     ]

    ExpM dl   = deadlockFree ci
    body = unlines [ unlines (prettyPrint <$> initialState ci)
                   , unlines (prettyPrint <$> initialSched ci)
                   , prettyPrint (initialCall ci)
                   , printRules ci rs dl
                   , prettyPrint (totalCall ci)
                   , ""
                   , initSpecOfConfig ci
                   ]



arbValStr = "instance (Arbitrary a) => Arbitrary (Val a) where \n\
\  arbitrary = oneof [ return VUnit \n\
\                    , return VUnInit \n\
\                    , VInt    <$> arbitrary \n\
\                    , VString <$> arbitrary \n\
\                    , VPid    <$> arbitrary \n\
\                    , VInL    <$> arbitrary \n\
\                    , VInR    <$> arbitrary \n\
\                    , VPair   <$> arbitrary <*> arbitrary ]"

arbVecStr="instance (Arbitrary a) => Arbitrary (Vec a) where \n\
\   arbitrary = do a <- arbitrary \n\
\                  return $ mkVec a"

printQCFile :: ConfigInfo Int -> [Rule HaskellModel] -> String
printQCFile ci _
  = unlines lhFile
  where
    lhFile = [ prettyPrint modVerify
             , ""
             ] ++ spec
    modVerify = Module noLoc (ModuleName "QC") [] Nothing (Just exports) imports decls
    exports   = []
    decls     = []
    imports   = mkImport <$> [ "SymVector"
                             , "SymMap"
                             , "SymVerify"
                             , "SymBoilerPlate"
                             , "Language.Haskell.Liquid.Prelude"
                             , "Test.QuickCheck"
                             ]
    mkImport m = ImportDecl { importLoc       = noLoc
                            , importModule    = ModuleName m
                            , importQualified = False
                            , importSrc       = False
                            , importAs        = Nothing
                            , importSpecs     = Nothing
                            , importSafe      = False
                            , importPkg       = Nothing
                            }
    spec =  "main :: IO ()"
            : (prettyPrint  $  qcMainFuncDecl ci) : ""
            : arbValStr : ""
            : arbVecStr : ""
            : concatMap (\s -> [s,""]) (prettyPrint <$> arbitraryDecls ci)


arbitraryDecls :: ConfigInfo Int -> [Decl]
arbitraryDecls ci = [ arbitraryPidPreDecl ci
                    , arbitraryStateDecl  ci ]

-- main =  do quickCheck
--              (\s plist -> runState s ... (getList plist) == ())
qcMainFuncDecl    :: ConfigInfo Int -> Decl
qcMainFuncDecl ci =  FunBind [ Match noLoc (name "main") [] Nothing (UnGuardedRhs rhs) Nothing ]
                     where pvarn n    = pvar $ name n
                           varn n     = Var $ UnQual $ name n
                           emptyVec p = vExp $ if isAbs p then "emptyVec2D" else "emptyVec"
                           bufs       = [ emptyVec p | p <- pids ci, _ <- tyMap ci ]
                           pidl       = varn "plist"
                           exp2       = appFun (varn runState) ((varn "s") : bufs ++ [pidl])
                           f          = Lambda noLoc
                                                 [pvarn "s", pvarn "plist"]
                                                 (InfixApp exp2
                                                             (QConOp $ UnQual $ Symbol "==")
                                                             (Con $ Special $ UnitCon))
                           exp        = App (varn "quickCheck") (Paren f)
                           rhs        = Do [Qualifier exp]

-- instance Arbitrary Pid_pre where
--         arbitrary = elements [...]
arbitraryPidPreDecl    :: ConfigInfo Int -> Decl
arbitraryPidPreDecl ci =  InstDecl noLoc Nothing [] [] tc_name [tv_name] [InsDecl (FunBind [arb])]
                          where tc_name = UnQual $ name "Arbitrary"
                                tv_name = TyVar $ name pidPre
                                var' s  = var $ name s
                                pid_ts  = [ var' $ pidConstructor p | p <- (pids ci) ]
                                arb_rhs = UnGuardedRhs (app (var' "elements") (listE pid_ts))
                                arb     = Match noLoc (name "arbitrary") [] Nothing arb_rhs Nothing

-- instance Arbitrary State where
--         arbitrary
--           = State <$> .. <*> ...
arbitraryStateDecl    :: ConfigInfo Int -> Decl
arbitraryStateDecl ci =  InstDecl noLoc Nothing [] [] tc_name [tv_name] [InsDecl (FunBind [arb])]
                         where tc_name   = UnQual $ name "Arbitrary"
                               tv_name   = TyVar $ name stateRecordCons
                               var' s    = var $ name s
                               fmap' f x = InfixApp f (QConOp $ UnQual $ Symbol "<$>") x
                               fapp' f g = InfixApp f (QConOp $ UnQual $ Symbol "<*>") g
                               vh:vt     = stateVarArbs ci
                               gen_exp   = foldl (\e v -> fapp' e v)
                                                 (fmap' (Con $ UnQual $ name stateRecordCons) vh)
                                                 vt
                               arb_rhs   = UnGuardedRhs $ gen_exp
                               arb       = Match noLoc (name "arbitrary") [] Nothing arb_rhs Nothing

-- for each field of the state record, use "return 0" for the integers and
-- "arbitrary" for the rest of the generators
stateVarArbs    :: ConfigInfo Int -> [Exp]
stateVarArbs ci = pcFs ++ ptrFs ++ valVarFs ++ intVarFs ++ absFs ++ globFs
                  where vararb   = var $ name $ "arbitrary"
                        ret0     = app (var $ name "return") (Lit $ Int 0)
                        pcFs     = [ ret0 | p <- pids ci ]
                        ptrFs    = [ ret0 | p <- pids ci, t <- fst <$> tyMap ci] ++
                                   [ ret0 | p <- pids ci, t <- fst <$> tyMap ci]
                        valVarFs = [ vararb | (p, v) <- valVars (stateVars ci) ]
                        intVarFs = [ vararb | (p, v) <- intVars (stateVars ci) ]
                        absFs    = concat [ [vararb, vararb, vararb] | p <- pids ci, isAbs p ]
                        globFs   = [ vararb | v <- globVals (stateVars ci) ]
