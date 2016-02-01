{-# Language ParallelListComp #-}
module Symmetry.IL.Render.HaskellModel where

import           Data.Char
import           Data.List
import           Data.Maybe
import           Data.Function
import           Language.Haskell.Exts.SrcLoc
import           Language.Haskell.Exts.Syntax hiding (Rule)
import           Language.Haskell.Exts.Build
import           Language.Haskell.Exts.Pretty

import           Symmetry.IL.AST
import           Symmetry.IL.Model
import           Symmetry.IL.Render.Horn.Config  
  
data HaskellModel = ExpM Exp
                  | PatM Pat
                  | StateUpM [(String, Exp)] [((Pid, ILType), Exp)]

-- Convenience Functions                    
vExp :: String -> Exp
vExp = var . name

opEq, opAnd, opPlus, opLt :: QOp
opEq   = op (sym "==")
opAnd  = op (sym "&&")
opPlus = op (sym "+")
opLt   = op (sym "<")

---------------------
-- Type Declarations
---------------------
intType  = TyCon (UnQual (name "Int"))
valType  = TyCon (UnQual (name "Val"))
mapTyCon = TyCon (UnQual (name "Map_t"))

mapType k v = TyApp (TyApp mapTyCon k) v

stateRecord :: [([Name], Type)] -> QualConDecl
stateRecord fs
  = QualConDecl noLoc [] [] (RecDecl (name stateRecordCons) fs)

  
stateDecl :: ConfigInfo Int
          -> [Decl]
stateDecl ci
  = [DataDecl noLoc DataType [] (name stateRecordCons) [] [stateRecord fs] []]
  where
    fs = pcFs ++ ptrFs ++ valVarFs ++ intVarFs
    pcFs     = [ mkInt p (pc p) | p <- pids ci ]
    ptrFs    = [ mkInt p (ptrR ci p t) | p <- pids ci, t <- fst <$> tyMap ci] ++
               [ mkInt p (ptrW ci p t) | p <- pids ci, t <- fst <$> tyMap ci]
    valVarFs = [ mkVal p v | (p, v) <- valVars (stateVars ci) ]
    intVarFs = [ mkInt p v | (p, v) <- intVars (stateVars ci) ]

    mkVal p v = if isAbs p then
                  ([name v], mapType intType valType)
                else
                  ([name v], valType)

    mkInt p v = if isAbs p then
                  ([name v], mapType intType intType)
                else
                  ([name v], intType)

pidDecl :: ConfigInfo Int
        -> [Decl]
pidDecl ci
  = [ DataDecl noLoc DataType [] (name pidPre) tvbinds cons []
    , TypeDecl noLoc (name pidType) [] pidPreApp
    ]
  where
    pidPreApp = foldl' TyApp (TyCon . UnQual $ name pidPre) (const intType <$> ts)
    mkPidCons  pt     = QualConDecl noLoc [] [] (mkPidCons' pt)
    mkPidCons' (p, t) = if isAbs p then
                          ConDecl (name (pidConstructor p)) [TyVar t]
                        else
                          ConDecl (name (pidConstructor p)) []
                          

    cons        = mkPidCons <$> ts
    tvbinds     = [ UnkindedVar t | (p, t) <- ts, isAbs p  ]
    ts          = [ (p, mkTy t) | p <- pids ci | t <- [0..] ]
    mkTy        = name . ("p" ++) . show

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

hAnd :: HaskellModel -> HaskellModel -> HaskellModel
hAnd (ExpM e1) (ExpM e2)
  = ExpM $ paren (infixApp e1 opAnd e2)

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

hIncr :: HaskellModel -> HaskellModel
hIncr (ExpM e)
  = ExpM $ (infixApp e opPlus (intE 1))

hSetFields :: ConfigInfo Int
           -> Pid
           -> [(String, HaskellModel)]
           -> HaskellModel
hSetFields ci (PConc _) ups
  = StateUpM [ (f, e) | (f, ExpM e) <- ups ] []
hSetFields ci p ups
  = StateUpM [ (f, putMap (vExp f) (vExp $ pidIdx p) e) | (f, ExpM e) <- ups ] []

hSetPC ci p (ExpM e)
  = StateUpM [ (pc p, e) ] []

con :: String -> Exp             
con = Con . UnQual . name

hExpr :: Pid -> ILExpr -> HaskellModel
hExpr p EUnit    = ExpM $ con unitCons    
hExpr p (EPid q@(PConc _)) = ExpM $ App (con pidCons) (vExp $ pidConstructor q)

-- Buffers
pidConstructor :: Pid -> String
pidConstructor = (toUpper <$>) . pid

pidPattern :: Pid -> Pat
pidPattern p@(PConc _)
  = PApp (UnQual (name (pidConstructor p))) []
pidPattern p@(PAbs (GV v) _)
  = PParen (PApp (UnQual (name (pidConstructor p))) [pvar (name v)])
pidPattern _ = error "pidPattern: non conc or abs"

hReadPtrR ci p t
  = hReadState ci p (ptrR ci p t)

hIncrPtrR ci p t
  = hSetFields ci p [(ptrR ci p t, hIncr ptrRExp)]
  where
    ptrRExp = hReadPtrR ci p t

hIncrPtrW ci p q t
  = hSetFields ci p [(ptrW ci q t, hIncr ptrWExp)]
  where
    ptrWExp = hReadPtrW ci p q t

hReadPtrW ci p q t
  = hReadState ci p (ptrW ci q t)

hPutMessage ci p q (e,t)
  = StateUpM [] [((q, t), e')]
  where
    ExpM e' = hExpr p e

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
          -> String
          -> ILExpr
          -> Rule HaskellModel
          -> Rule HaskellModel
hMatchVal ci p f (EPid q) (Rule p' ms grd ups)
  = Rule p' ((f, PatM $ pidPattern q) : ms) grd ups

hRule :: ConfigInfo Int
      -> Pid
      -> HaskellModel
      -> HaskellModel
      -> Rule HaskellModel
hRule _ p g us
  = Rule p [] g us

hJoinUpdates _ _ (StateUpM us bufs) (StateUpM us' bufs')
  = StateUpM (us ++ us') (bufs ++ bufs')
    
instance ILModel HaskellModel where 
  int        = hInt
  incr       = hIncr
  lt         = hLt
  eq         = hEq
  and        = hAnd
  readState  = hReadState
  readPtrR   = hReadPtrR
  readPtrW   = hReadPtrW
  readPC     = hReadPC

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
printRules ci rs = prettyPrint $ FunBind matches
  where
    matches = mkMatch <$> perPid
    mkMatch rules
      = Match noLoc (name "runState") (pat (rulesPid rules)) Nothing (mkGuardedRhss rules) Nothing 
    mkGuardedRhss rules
      = GuardedRhss [ mkRhs p ms grd fups bufups | Rule p ms (ExpM grd) (StateUpM fups bufups) <- rules ]
    mkRhs p [] grd fups bufups
      = GuardedRhs noLoc [Qualifier grd] (mkCall p fups bufups)
    mkRhs p ms grd fups bufups
      = GuardedRhs noLoc [Qualifier grd] (mkCase ms (mkCall p fups bufups))
    mkCase [(f, PatM p)] e
      = Case (vExp f) [Alt noLoc p (UnGuardedRhs e) Nothing]
    mkRecUp p fups
      = RecUpdate (vExp state) [mkFieldUp p f e | (f,e) <- fups]
    mkFieldUp p f e
      = FieldUpdate (UnQual (name f)) e
    mkCall p fups bufups
      = metaFunction "runState"
          (mkRecUp p fups : mkBufUps bufups ++ [vExp "sched"]) 
    mkBufUps bufups
      = [ findUp p t bufups | p <- pids ci, t <- fst <$> tyMap ci]

    rulesPid rules = let Rule p _ _ _ = head rules in p
    pidRule (Rule p _ _ _) = p
    eqPid  = (==) `on` pidRule
    perPid = groupBy eqPid $ sortBy (compare `on` pidRule) rs

    pat p = [ PAsPat (name state) (PRec (UnQual (name stateRecordCons)) [PFieldWildcard]) ] ++
            [ pvar (name (buf ci p t)) | p <- pids ci, t <- fst <$> tyMap ci ] ++
            [ PInfixApp (pidPattern p) list_cons_name (pvar (name "sched")) ]

    findUp p t bufups = maybe (vExp $ buf ci p t) (putVec (vExp $ buf ci p t) (vExp $ ptrW ci p t)) $
                        lookup (p, t) bufups
          
printHaskell :: ConfigInfo Int -> [Rule HaskellModel] -> String
printHaskell ci rs = unlines (printRules ci rs : (prettyPrint <$> decls))
  where
     decls = stateDecl ci ++ pidDecl ci
