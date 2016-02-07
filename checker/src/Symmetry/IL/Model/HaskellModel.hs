{-# Language ParallelListComp #-}
module Symmetry.IL.Model.HaskellModel where

import           Data.Char
import           Data.List
import           Data.Maybe
import           Data.Function
import           Language.Haskell.Exts.SrcLoc
import           Language.Haskell.Exts.Syntax hiding (Rule, EVar)
import           Language.Haskell.Exts.Build
import           Language.Haskell.Exts.Pretty
import           Symmetry.IL.Model.HaskellSpec (initSpecOfConfig)

import           Symmetry.IL.AST
import           Symmetry.IL.Model
import           Symmetry.IL.ConfigInfo
import           Symmetry.IL.Model.HaskellDefs
import           Symmetry.IL.Model.HaskellDeadlock
  
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
  = paren (app (app (app (app (vExp vecPutFn) key1) key2) val) m)

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
hExpr _ p EUnit    = ExpM $ con unitCons    
hExpr _ p (EPid q@(PConc _)) = ExpM $ App (con pidCons) (vExp $ pidConstructor q)
hExpr ci p (EVar (V v))
  = hReadState ci p v
hExpr ci p (ELeft e)
  = ExpM $ App (con leftCons) (unExp $ hExpr ci p e)
hExpr ci p (ERight e)
  = ExpM $ App (con rightCons) (unExp $ hExpr ci p e)

hPred :: ConfigInfo Int -> Pid -> ILPred -> HaskellModel
hPred ci _ ILPTrue
  = ExpM $ vExp "True"
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


ilExpPat (EPid q)
  = PApp (UnQual (name pidCons)) [pidPattern q]
ilExpPat (ELeft (EVar (V v)))
  = PApp (UnQual (name leftCons)) [pvar (name v)]
ilExpPat (ERight (EVar (V v)))
  = PApp (UnQual (name rightCons)) [pvar (name v)]

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
      = metaFunction "liquidAssert"
         [e, paren (mkCall p Nothing fups bufups)]
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
    dlRhs      = UnGuardedRhs (metaFunction "liquidAssert" [dl, unit_con])
    dlpat      = pat (pids ci)

    findUp p t bufups = maybe (vExp $ buf ci p t) (putVec (vExp $ buf ci p t) (vExp $ ptrW ci p t)) $
                        lookup (p, t) bufups

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
                     , "module SymVerify () where"
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
                   , ""
                   , initSpecOfConfig ci
                   ]
