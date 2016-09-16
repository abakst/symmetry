{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ParallelListComp #-}
module Symmetry.IL.Model.HaskellModel where

import qualified Control.Monad.State as S
import           Data.Generics
import           Data.List
import           Data.Maybe
import           Data.Function
import           Text.Printf
import           Language.Haskell.Exts.SrcLoc
import           Language.Haskell.Exts.Syntax as H hiding (Rule, EVar)
import           Language.Haskell.Exts.Build
import           Language.Haskell.Exts.Pretty
import           Symmetry.IL.AST as IL
import           Symmetry.IL.Model
import           Symmetry.IL.Deadlock
import           Symmetry.IL.ConfigInfo
import           Symmetry.IL.Model.HaskellDefs
import           Symmetry.IL.Model.HaskellSpec ( initSpecOfConfig
                                               , withStateFields
                                               , defaultVisitor
                                               , StateFieldVisitor(..)
                                               )
---------------------------------
-- Wrapper type for Haskell code
---------------------------------
data HaskellModel = ExpM { unExp :: Exp }
                  | PatM { unPat :: H.Pat }
                  | StateUpM [(String, Exp)] [((Pid, IL.Type), Exp)]
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

cons :: Exp -> Exp -> Exp
cons x y = paren (InfixApp x (QConOp list_cons_name) y)

neg :: Exp
neg = vExp "not"

setInsert :: Exp -> Exp -> Exp
setInsert i s
  = metaFunction "union" [metaFunction "singleton" [i], s]

setDelete :: Exp -> Exp -> Exp
setDelete i s
  = metaFunction "difference" [s, metaFunction "singleton" [i]]
---------------------
-- Logicify
---------------------
logicify :: ConfigInfo a -> Exp -> Exp -> Exp
logicify ci s e
  = everywhere (mkT go) e
  where
    fields = withStateFields ci defaultVisitor
    go :: Exp -> Exp
    go (If e1 e2 e3) = If (p e1) (p e2) (p e3)
    go e'@(Var (UnQual (Ident i)))
      | i `elem` fields   = metaFunction i [s]
      | i == mapGetFn     = vExp $ "Map_select"
      | i == mapPutFn     = vExp $ "Map_store"
      | i == "union"      = vExp $ "Set_cup"
      | i == "difference" = vExp $ "Set_dif"
      | i == "singleton"  = vExp $ "Set_sng"
      | otherwise       = e'
    go e' = e'
    p e'@(Paren _) = e'
    p e'           = Paren e'
      

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

hEmptySet :: HaskellModel
hEmptySet = ExpM (vExp "empty")

hUnion :: HaskellModel -> HaskellModel -> HaskellModel
hUnion (ExpM e1) (ExpM e2)
  = ExpM $ metaFunction "union" [e1, e2]
hUnion e1 e2
  = error (printf "hUnion %s %s" (show e1) (show e2))

hReadState :: ConfigInfo a
           -> Pid
           -> Pid
           -> String
           -> HaskellModel
hReadState _ _ (PConc _) f
  = ExpM $ vExp f
hReadState ci p@(PAbs (GV _) _) q@(PAbs (V idx) _) f
  = ExpM $ getMap (vExp f) i
  where
    ExpM i = hReadState ci p p idx
hReadState _ p q f
  = ExpM $ getMap (vExp f) (vExp (pidIdx q))

hIsUnfold ci p@(PAbs (GV v) _)
  = ExpM $ paren (infixApp e1 opEq e2)
  where
    e1 = vExp (pidUnfold p)
    e2 = vExp v

hReadPC :: ConfigInfo a
        -> Pid
        -> Pid
        -> HaskellModel
hReadPC ci p q
  = hReadState ci p q (pc q)

hReadPCCounter :: ConfigInfo a
               -> Pid
               -> HaskellModel
hReadPCCounter ci p
  = ExpM . vExp $ pcCounter p

hMovePCCounter :: ConfigInfo a
               -> Pid
               -> HaskellModel
               -> HaskellModel
               -> HaskellModel
hMovePCCounter ci p (ExpM i) (ExpM j)
  = ExpM $ putMap (putMap m i (dec (getMap m i)))
                  j
                  (inc (getMap m j))
    where
      dec e = infixApp e opMinus (intE 1)
      inc e = infixApp e opPlus (intE 1)
      m = unExp $ hReadPCCounter ci p

hReadMap :: HaskellModel
         -> HaskellModel
         -> HaskellModel
hReadMap (ExpM m) (ExpM i)
  = ExpM $ getMap m i

hReadSetBound :: ConfigInfo a
              -> Pid
              -> Set
              -> HaskellModel
hReadSetBound ci p (S s)
  = hReadState ci p p s
-- Essentially inlining the var lookup
hReadSetBound ci p (SV v)
  = ExpM e
  where
    e = caseSplitSets ci p v go
    go (Known _ i)       = intE (toInteger i)
    go (Unknown _ (V s)) = vExp s
hReadSetBound _ _ (SInts s)
  = hInt s

caseSplitSets :: ConfigInfo a -> Pid -> Var -> (SetBound -> Exp) -> Exp
caseSplitSets ci p (V v) g
  = caseE caseExp cases
  where
    caseExp             = unExp (hReadState ci p p v)
    (ks, us)            = allSets ci
    mkAlt b@(Known k i)       = alt noLoc (mkPat k) (g b)
    mkAlt b@(Unknown u (V v)) = alt noLoc (mkPat u) (g b)
    mkPat (S u)         = metaConPat setCons [strP u]
    cases    = mkAlt <$> (ks ++ us)

hReadRoleBound :: ConfigInfo a
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

hSetFields :: ConfigInfo a
           -> Pid
           -> Pid
           -> [(String, HaskellModel)]
           -> HaskellModel
hSetFields ci p (PConc _) ups
  = StateUpM [ (f, e) | (f, ExpM e) <- ups ] []
hSetFields ci p q@(PAbs (V v) _) ups
  = StateUpM [ (f, putMap (vExp f) (unExp $ hReadState ci p p v) e) | (f, ExpM e) <- ups] []
hSetFields ci _ q ups
  = StateUpM [ (f, putMap (vExp f) (vExp $ pidIdx q) e) | (f, ExpM e) <- ups ] []

hSetPC ci p e
  = hSetFields ci p p [(pc p, e)]

hSetPCCounter :: ConfigInfo a
              -> Pid
              -> HaskellModel
              -> HaskellModel
hSetPCCounter ci p e
  = StateUpM [(pcCounter p, unExp e)] []

con :: String -> Exp             
con = Con . UnQual . name

isIntVar :: ConfigInfo a -> String -> Bool
isIntVar ci v
  = v `elem` (snd <$> intVars (stateVars ci))

hIte :: HaskellModel
     -> HaskellModel
     -> HaskellModel
     -> HaskellModel
hIte (ExpM b) (ExpM e1) (ExpM e2)
  = ExpM $ If b e1 e2
hIte _ _ _
  = error "hIte (non expressions)"

pidExp :: Pid -> Exp
pidExp p@(PConc _)
  = vExp $ pidConstructor p
pidExp p@(PAbs _ _)
  = App (vExp $ pidConstructor p) (vExp $ pidIdx p)

hExpr :: Bool -> ConfigInfo a -> Pid -> ILExpr -> HaskellModel
hExpr _ _ _ EUnit    = ExpM $ con unitCons    
hExpr _ _ _ EString  = ExpM $ App (con stringCons) (strE "<str>")
hExpr _ _ _ (EInt i) = hInt i
hExpr _ _ _ (ESet (S s))
  = ExpM $ app (con setCons) (strE s)
hExpr b ci p (ESet (SV v))
  = hExpr b ci p (EVar v)
hExpr _ ci p (EPid q@(PAbs (V v) _))
  = ExpM $ App (con pidCons) (App (vExp $ pidConstructor q) (unExp $ readState ci p p v))
hExpr _ _ _ (EPid q)
  = ExpM $ App (con pidCons) (pidExp q)

hExpr _ _ _ (EVar (GV v))
  = ExpM . vExp $ v
hExpr _ ci p (EVar (VPtrR t))
  = readPtrR ci p p t
hExpr _ ci p (EVar (VPtrW t))
  = readPtrW ci p p t
hExpr b ci p (EVar (V v))
  = if b && isIntVar ci v then
      ExpM $ Paren (App (con intCons) (unExp $ hReadState ci p p v))
    else
      hReadState ci p p v
hExpr _ ci p (EVar (VRef q v))
  = hReadState ci p q v
hExpr b ci p (ELeft e)
  = ExpM $ App (con leftCons) (unExp $ hExpr b ci p e)
hExpr b ci p (ERight e)
  = ExpM $ App (con rightCons) (unExp $ hExpr b ci p e)
hExpr b ci p (EPair e1 e2)
  = ExpM $ App (App (con pairCons) (unExp $ hExpr b ci p e1))
               (unExp $ hExpr b ci p e2)
hExpr _ ci p (EPlus e1 e2)
  = ExpM $ infixApp e1' opPlus e2'
  where
    e1' = unExp $ hExpr False ci p e1
    e2' = unExp $ hExpr False ci p e2
hExpr b ci p (EProj1 e)
  = ExpM $ metaFunction "vLeft" [unExp $ hExpr b ci p e]
hExpr b ci p (EProj2 e)
  = ExpM $ metaFunction "vRight" [unExp $ hExpr b ci p e]

hExpr _ _ _ e
  = error (printf "hExpr: TBD(%s)" (show e))

hPred :: ConfigInfo a -> Pid -> Pred -> HaskellModel
hPred _ _ ILPTrue
  = ExpM $ vExp "True"
hPred ci p (ILNot b)
  = ExpM $ (paren (metaFunction "not" [unExp $ hPred ci p b]))
hPred ci p (ILAnd b1 b2)
  = ExpM $ InfixApp (unExp $ hPred ci p b1) opAnd (unExp $ hPred ci p b2)
hPred ci p (ILOr b1 b2)
  = ExpM $ InfixApp (unExp $ hPred ci p b1) opOr (unExp $ hPred ci p b2)
hPred ci p (ILBop o e1 e2)
  = ExpM $ paren (infixApp (unExp $ hExpr False ci p e1)
                           (qop o)
                           (unExp $ hExpr False ci p e2))
  where
    qop Eq = opEq
    qop Lt = opLt
    qop Le = opLte
    qop Gt = opGt
    qop Ge = opGte

hReadPtrR ci p q t
  = hReadState ci p q (ptrR ci q t)

hIncrPtrR ci p t
  = hSetFields ci p p [(ptrR ci p t, hIncr ptrRExp)]
  where
    ptrRExp = hReadPtrR ci p p t

hIncrPtrW ci p q t
  = hSetFields ci p q [(ptrW ci q t, hIncr ptrWExp)]
  where
    ptrWExp = hReadPtrW ci p q t

-- hReadPtrW ci p q@(PAbs (V v) _) t
--   = ExpM $ getMap (vExp (ptrW ci q t)) i
--   where
--     i = unExp $ hReadState ci p v
hReadPtrW ci p q t
  = hReadState ci p q (ptrW ci q t)

hPutMessage ci p q (e,t)
  = StateUpM [] [((q, t), e')]
  where
    ExpM e' = hExpr True ci p e

hGetMessage ci p@PConc{} (V v, t)
  = hSetFields ci p p [(v, ExpM $ getVec (vExp (buf ci p t)) e')]
  where
    ExpM e' = hReadPtrR ci p p t

hGetMessage ci p@(PAbs (GV i) _) (V v, t)
  = hSetFields ci p p [(v, ExpM $ getVec2D (vExp (buf ci p t)) (vExp i) e')]
  where
    ExpM e' = hReadPtrR ci p p t

hMatchVal :: ConfigInfo a
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

hNonDet :: ConfigInfo a
        -> Pid
        -> HaskellModel
        -> HaskellModel
hNonDet _ _ (ExpM e)
  = ExpM $ metaFunction nondet [vExp sched, e]
hNonDet _ _ _
  = error "hNonDet non exp"

hNonDetRange :: ConfigInfo a
             -> Pid
             -> Set
             -> HaskellModel
hNonDetRange ci p (S s)
  = ExpM $ metaFunction nondetRange [intE 0, unExp $ readState ci p p s]
hNonDetRange _ _ _
  = error "hNonDetRange (TBD)"

hRule :: ConfigInfo a
      -> Pid
      -> HaskellModel
      -> Maybe (HaskellModel)
      -> HaskellModel
      -> Rule HaskellModel
hRule _ p g assert us
  = Rule p g assert us

hJoinUpdates _ _ (StateUpM us bufs) (StateUpM us' bufs')
  = StateUpM (us ++ us') (bufs ++ bufs')

hBlockedCounter :: ConfigInfo a
                -> Pid
                -> Pid
                -> HaskellModel
hBlockedCounter ci p q
  = ExpM (vExp $ numBlocked ci q)

hSetBlockedCounter :: ConfigInfo a
                   -> Pid
                   -> Pid
                   -> HaskellModel
                   -> HaskellModel
hSetBlockedCounter ci p q e
  = StateUpM [(numBlocked ci q, unExp e)] []
  
hReadEnabled :: ConfigInfo a
             -> Pid
             -> HaskellModel
hReadEnabled ci p
  = ExpM (vExp $ enabledSet ci p)

hSetEnabled :: ConfigInfo a
            -> Pid
            -> HaskellModel
            -> HaskellModel
hSetEnabled ci p e
  = StateUpM [(enabledSet ci p, unExp e)] []

hEnable :: ConfigInfo a
        -> Pid
        -> Pid
        -> HaskellModel
hEnable ci p q
  = ExpM $ setInsert i (vExp (enabledSet ci q))
    where
      i = enabledIdx ci p q

hDisable :: ConfigInfo a
         -> Pid
         -> Pid
         -> HaskellModel
hDisable ci p q
  = ExpM $ setDelete i (vExp (enabledSet ci q))
    where
      i = enabledIdx ci p q

enabledIdx :: ConfigInfo a
           -> Pid
           -> Pid
           -> Exp
enabledIdx ci p (PAbs (V v) _)
  = unExp $ hReadState ci p p v
enabledIdx ci p (PAbs (GV v) _)
  = vExp v
enabledIdx ci p q
  = error (printf "hEnable(%s)" (show q))

instance ILModel HaskellModel where 
  int        = hInt
  add        = hAdd
  incr       = hIncr
  decr       = hDecr
  expr       = hExpr True
  pred       = hPred
  lt         = hLt
  lte        = hLte
  eq         = hEq
  and        = hAnd
  or         = hOr
  lneg       = hLNeg
  true       = hTrue
  false      = hFalse
  ite        = hIte
  readMap    = hReadMap
  readSetBound = hReadSetBound
  readState  = hReadState
  readPtrR   = hReadPtrR
  readPtrW   = hReadPtrW
  readPC     = hReadPC
  readPCCounter = hReadPCCounter
  movePCCounter = hMovePCCounter
  readRoleBound = hReadRoleBound
  nonDet = hNonDet
  nonDetRange = hNonDetRange
  isUnfold = hIsUnfold
  readEnabled = hReadEnabled
  enable = hEnable
  disable = hDisable
  emptySet = hEmptySet
  union    = hUnion

  joinUpdate = hJoinUpdates
  setPC      = hSetPC
  setState   = hSetFields
  setPCCounter = hSetPCCounter
  setEnabled = hSetEnabled
  incrPtrR   = hIncrPtrR
  incrPtrW   = hIncrPtrW
  putMessage = hPutMessage
  getMessage = hGetMessage

  rule       = hRule
  matchVal   = hMatchVal
  printModel = printHaskell
  printCheck = printQCFile

ilExpPat :: ILExpr -> H.Pat
ilExpPat (EPid q)
  = PApp (UnQual (name pidCons)) [pidPattern q]
ilExpPat (ELeft (EVar v))
  = PApp (UnQual (name leftCons)) [varPat v]
ilExpPat (ERight (EVar v))
  = PApp (UnQual (name rightCons)) [varPat v]
ilExpPat (ESet (S n))
  = metaConPat setCons [strP n]
ilExpPat e
  = error (printf "ilExpPath TODO(%s)" (show e))

varPat :: Var -> H.Pat    
varPat (V v)  = pvar $ name v
varPat (GV v) = pvar $ name v

type TxList = [(Pid, String, Maybe Exp, [(String, Exp)])]
data RuleState = RS { txCtr :: Int
                    , txList :: TxList
                    }

declRules :: ConfigInfo a -> [Rule HaskellModel] -> Exp -> Exp -> S.State RuleState Decl
declRules ci rs cond done = FunBind <$> matches
  where
    matches     = do ms <- ruleMatches
                     return (ms ++ [mkDlMatch])
    ruleMatches = mapM mkMatch perPid
    mkMatch rules
      = do m <- Match noLoc (name runState) (pat True [rulesPid rules]) Nothing <$> mkGuardedRhss rules <*> return Nothing 
           S.modify $ \s -> s { txCtr = 0 }
           return m
    mkGuardedRhss rules
      = do rhss <- mapM (\(Rule p (ExpM grd) a up) -> mkRhs p grd a up) rules
           return $ GuardedRhss rhss
    mkRhs p grd a (GuardedUpM f cases)
      = do alts <- mapM (mkAlt p a) cases
           return $ GuardedRhs noLoc [Qualifier grd] (H.Case f alts)
    mkRhs p grd a (StateUpM fups bufups)
      = do call <- mkCall ci p a fups bufups
           return $ GuardedRhs noLoc [Qualifier grd] call
    -- mkRhs p ms grd fups bufups
    --   = GuardedRhs noLoc [Qualifier grd] (mkCall p fups bufups)
    mkAlt p a (ile, StateUpM fups bufups)
      = do call <- mkCall ci p a fups bufups
           return $ Alt noLoc (ilExpPat ile) (UnGuardedRhs call) Nothing
    rulesPid rules = let Rule p _ _ _ = head rules in p
    pidRule (Rule p _ _ _) = p
    eqPid  = (==) `on` pidRule
    perPid = groupBy eqPid $ sortBy (compare `on` pidRule) rs

    pat b ps = [ PAsPat (name state) (PRec (UnQual (name stateRecordCons)) [PFieldWildcard]) ] ++
               [ pvar (name (buf ci q t)) | q <- pids ci, t <- fst <$> tyMap ci ] ++
               [ mkSchedPat b ps ] ++
               (ifQC ci (pvar (name "qc_ss")))

    mkSchedPat b ps = if b then
                        foldr (\q rest -> PInfixApp (pidPattern q) list_cons_name rest) schedPVar ps
                      else
                        PList [pidPattern p | p <- ps]
    schedPVar  = pvar (name sched)

    mkDlMatch  = Match noLoc (name runState) dlpat Nothing (GuardedRhss [dlRhs]) Nothing
    dlRhs      = GuardedRhs noLoc [Qualifier cond] (mkAssert (Just (ExpM done)) (if isQC ci
                                                                                 then (var $ name "qc_ss")
                                                                                 else unit_con))
    dlpat      = pat False . concat $ [[univAbs p, extAbs p] | p <- pids ci, isAbs p ]

readMsgUpdates :: [(String, Exp)] -> ([(String, Exp)], [(String, Exp)])
readMsgUpdates ups
  = partition isReadUpdate ups
  where
    isReadUpdate (_, e) = not . null $ listify isVecRead e
    isVecRead (Var (UnQual (Ident i))) = i == vec2DGetFn || i == vecGetFn
    isVecRead _                        = False

mkCall :: ConfigInfo a
       -> Pid
       -> Maybe HaskellModel
       -> [(String, Exp)]
       -> [((Pid, IL.Type), Exp)]
       -> S.State RuleState Exp 
mkCall ci p e fups bufups
  | isQC ci && isJust e
    = do n <- addTransitionM p e fups
         return . letDecl n $ eitherCall
  | isQC ci
    = do n <- addTransitionM p e fups
         return . letDecl n $ metaFunction runState (args "qc_s'")
  | otherwise
    = do n <- addTransitionM p e fups
         return $ metaFunction runState (args n)
  where
    letDecl n = Let (BDecls [PatBind noLoc (pvar nextState) (nextStateRhs n) Nothing]) 
    args n = [if isQC ci then vExp n else nextStateExp n] ++
             mkBufUps bufups ++
             [vExp sched] ++
             ifQC ci (Paren $ infix_syn ":"
                      (tuple [var nextState, pidExp p])
                      (var $ name "qc_ss"))
              
    (bufReads,_) = readMsgUpdates fups
             
    nextState = name "qc_s'"
    nextStateRhs n = UnGuardedRhs (nextStateExp n)
    nextStateExp n
      = metaFunction n ([vExp state] ++
                        [ vExp (pidIdx p) | isAbs p ] ++
                        [ paren readExp | (_, readExp) <- bufReads ])
    eitherCall =
      metaFunction "either"
        [ lamE noLoc [PWildCard] (App (Con . UnQual $ name "Left") (vExp "qc_ss"))
        , lamE noLoc [pvar nextState] (metaFunction runState (args state))
        , var nextState
        ]
    mkBufUps bufups
      = [ findUp p t bufups | p <- pids ci, t <- fst <$> tyMap ci]
    findUp q t bufups
      = maybe (vExp $ buf ci q t) (\(q, e) -> updateBuf ci p q t e) $ findUpdate q t bufups

addTransitionM :: Pid -> Maybe HaskellModel -> [(String, Exp)] -> S.State RuleState String
addTransitionM p e fups
  = do n <- S.gets txCtr
       let tx = printf "t_%s_%d" (pid p) n
       S.modify $ \s -> RS { txCtr = n + 1
                           , txList = (p, tx, e', fups) : txList s
                           }
       return tx
  where
    e' = (\(ExpM e') -> e') <$> e
        
mkAssert (Just (ExpM e)) k
  = infixApp (metaFunction "liquidAssert" [e]) (op . sym $ "$") k
mkAssert Nothing k
  = k

updateBuf :: ConfigInfo a -> Pid -> Pid -> IL.Type -> Exp -> Exp
updateBuf ci p q@(PAbs (V idx) _) t e
  = putVec2D v i j e 
    where
      v = vExp $ buf ci q t
      i = if isAbs p then
            unExp (hReadState ci p p idx)
          else
            vExp $ pidIdx q
      j = if isAbs p then
            getMap (vExp $ ptrW ci q t) (unExp (hReadState ci p p idx))
          else
            getMap (vExp $ ptrW ci q t) (vExp $ pidIdx q)
updateBuf ci p q@(PAbs _ _) t e
  = putVec2D v i j e 
    where
      v = vExp $ buf ci q t
      i = vExp $ pidIdx q
      j = getMap (vExp $ ptrW ci q t) (vExp $ pidIdx q)
updateBuf ci p q t e
  = putVec v i e
  where
    v = vExp $ buf ci q t
    i = vExp $ ptrW ci q t

findUpdate :: Pid -> IL.Type -> [((Pid, IL.Type), Exp)] -> Maybe (Pid, Exp)
findUpdate (PAbs _ s) t bufups
  = case [ (p, e) | ((p@(PAbs _ s'), t'), e) <- bufups, s == s', t == t' ] of
      []  -> Nothing
      x:_ -> Just x
findUpdate p t bufups
  = (p,) <$> lookup (p, t) bufups

undef = "undefined"                               
undefinedExp = vExp undef

initialState :: ConfigInfo a -> [Decl]
initialState _
  = [ TypeSig noLoc [name initState] (TyCon (UnQual (name stateRecordCons)))
    , nameBind noLoc (name initState) undefinedExp
    ]

initialSched :: ConfigInfo a -> [Decl]
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

totalCall :: ConfigInfo a -> Decl
totalCall ci =
  FunBind [Match noLoc (name runState) args Nothing rhs Nothing]
    where
      args = [pvar (name state)] ++
             (pvar . name <$> bufArgs) ++
             [schedPat] ++
             ifQC ci (pvar (name ("states")))
      bufArgs = [ "a" ++ show i | i <- [0..] | _ <- pids ci, _ <- tyMap ci]
      rhs  = UnGuardedRhs $
              metaFunction runState
                ([vExp state] ++
                 (vExp <$> bufArgs) ++
                 [vExp "sched"] ++
                 ifQC ci (vExp "states"))
      schedPat = pParen (PInfixApp (pvar (name "s")) list_cons_name (pvar (name "sched")))

initialCall :: ConfigInfo a -> Decl
initialCall ci =
  nameBind noLoc (name "check") call
    where
      call = metaFunction runState (vExp initState : bufs ++ [initSchedCall] ++ ss)
      ss = ifQC ci emptyListCon
      bufs = [ emptyVec p | p <- pids ci, _ <- tyMap ci ]
      emptyVec p = vExp $ if isAbs p then emptyVec2DFn else emptyVecFn
      initSchedCall = metaFunction initSched [vExp initState]

transitionRules :: ConfigInfo a -> RuleState -> String
transitionRules ci RS { txList = m }
  = unlines (transitionRule ci <$> reverse m)

transitionRule :: ConfigInfo a -> (Pid, String, Maybe Exp, [(String, Exp)]) -> String
transitionRule ci (p, t, assert, updates)
  = if isAbs p then
      unlines [ printf "{-@ assume %s :: s0:{v:State | %s} -> %s:Int -> %s{s1:State | %s} @-}" t pre (pidIdx p) xtraSpec fieldUpdates
              , printf "%s :: State -> Int -> %sState" t xtraTy
              , prettyPrint tx 
              ]
    else
      unlines [ printf "{-@ assume %s :: s0:{v:State | %s} -> %s{s1:State | %s} @-}" t pre xtraSpec fieldUpdates 
              , printf "%s :: State -> %sState" t xtraTy
              , prettyPrint tx 
              ]
  where
    pre          = maybe "true" (\e -> printLine (logicify ci (vExp "v") e)) assert
    vars         = withStateFields ci defaultVisitor
    fieldUpdates = intercalate " && " [ mkUpdate f | f <- vars ]

    (bufReads,nonReads) = readMsgUpdates updates
    msgTy               = if isAbs p then "Map_t Int (Val Pid)" else "Val Pid"
    (xtraSpec, xtraTy, xtraArg)
      = case bufReads of
          [(f, _)] -> (printf "%s_e:(%s) -> " f msgTy, printf "%s -> " msgTy, readExp f)
          _        -> ("", "", "")
                   -- mkAssert e $ mkRecUp p fups

    mkUpdate :: String -> String
    mkUpdate f   = case lookup f updates of
                     Just e
                       | f `elem` (fst <$> nonReads) -> printf "%s s1 = %s" f (printLine (logicify ci (vExp "s0") e))
                       | otherwise                   -> printf "%s s1 = %s" f (readExp f)
                     Nothing -> printf "%s s1 = %s s0" f f

    printLine = prettyPrintWithMode defaultMode { layout = PPNoLayout }                                                   

    tx   = FunBind [body]
    body = runStateMatch t args (UnGuardedRhs (mkAssert (ExpM <$> assert) recUp))
    args = [PAsPat (name state) (PRec (UnQual (name stateRecordCons)) [PFieldWildcard])] ++
           [pvar $ name (pidIdx p) | isAbs p ] ++
           [pvar $ name xtraArg    | not (null bufReads) ]
    recUp
      = RecUpdate (vExp state) ([mkFieldUp p f e | (f,e) <- nonReads] ++
                                [mkReadUp p f e  | (f,e) <- bufReads])
    mkFieldUp _ f e
      = FieldUpdate (UnQual (name f)) e
    mkReadUp _ f _
      = FieldUpdate (UnQual (name f)) (vExp $ readExp f)

    readExp f = f ++ "_e"

runStateMatch f args rhs
  = Match noLoc (name f) args Nothing rhs Nothing
    -- logicalExp = 
          
printHaskell :: (Data a, Identable a)
             => ConfigInfo a -> [Rule HaskellModel] -> String
printHaskell ci rs = unlines [ header
                             , ""
                             , body
                             ]
  where
    header = unlines $ [ "{-# Language RecordWildCards #-}"
                       , "{-@ LIQUID \"--no-true-types\" @-}"
                       , "module SymVerify where"
                       , "import Data.Set"
                       , "import SymVector"
                       , "import SymMap hiding (singleton)"
                       , "import qualified SymMap (singleton)"
                       , "import SymBoilerPlate"
                       ] ++ (if isQC ci then [] else ["import Language.Haskell.Liquid.Prelude"])

    (ExpM cond, ExpM done) = deadlockFree ci
    (rules,ruleSt) = S.runState (declRules ci rs cond done) RS { txCtr = 0, txList = [] }
    body = unlines [ unlines (prettyPrint <$> initialState ci)
                   , unlines (prettyPrint <$> initialSched ci)
                   , prettyPrint (initialCall ci)
                   , prettyPrint rules
                   , prettyPrint (totalCall ci)
                   , transitionRules ci ruleSt
                   , ""
                   , initSpecOfConfig ci
                   ]

-- ######################################################################
-- ### QUICK CHECK ######################################################
-- ######################################################################

printQCFile :: (Data a, Identable a)
            => ConfigInfo a -> [Rule HaskellModel] -> String
printQCFile ci _
  = unlines lhFile
  where
    sep    = concatMap (\s -> [s,""])
    lhFile = sep (map unlines [header, spec])
    header = [ "{-# Language RecordWildCards #-}"
             , "{-# LANGUAGE OverloadedStrings #-}"
             , "module QC () where"
             , "import SymVector"
             , "import SymVector"
             , "import SymMap"
             , "import SymVerify"
             , "import SymBoilerPlate"
             , "import Test.QuickCheck"
             , "import Test.QuickCheck.Monadic"
             , "import Data.Aeson"
             , "import Data.Aeson.Encode.Pretty"
             , "import Control.Monad"
             , "import Data.ByteString.Lazy.Char8 as C (putStrLn, writeFile, appendFile, readFile)"
             , "import Data.HashMap.Strict as H hiding (map,filter,null)"
             , "import Data.Maybe"
             , "import Data.Either"
             , "import Data.String"
             , "import System.Directory"
             , "import System.Exit"
             ]
    spec =    qcDefsStr (qcSamples ci)
            : qcMainStr
            : (prettyPrint  $  runTestDecl ci) : ""
            : arbValStr : ""
            : arbVecStr : ""
            : sep (prettyPrint <$> arbitraryDecls ci)
            ++ sep (prettyPrint <$> jsonDecls ci)

emptyListCon = Con . Special $ ListCon
unitCon      = Con . Special $ UnitCon

ifQC ci x = [x | isQC ci]

infix_syn sym f g = InfixApp f (QConOp . UnQual $ Symbol sym) g
fmap_syn          = infix_syn "<$>"
fapp_syn          = infix_syn "<*>"

arbitraryDecls :: (Identable a, Data a) => ConfigInfo a -> [Decl]
arbitraryDecls ci = [ arbitraryPidPreDecl ci
                    , arbitraryStateDecl  ci ]

jsonDecls   :: ConfigInfo a -> [Decl]
jsonDecls ci = ($ ci) <$> [ stateFromJSONDecl
                          , stateToJSONDecl
                          , pidFromJSONDecl
                          , pidToJSONDecl     ]

-- ### QuickCheck helpers ##################################################

-- runTest (s,plist)
--   = let l = runState s emptyVec emptyVec plist []
--     in (reverse l, plist)

-- prop_runState :: State -> [Pid_pre] -> Property
-- prop_runState s plist = monadicIO $ do
--   let l = runState s emptyVec emptyVec plist []
--   in if null l
--         then return ()
--         else run (log_states l)
--   assert True
runTestDecl    :: ConfigInfo a -> Decl
runTestDecl ci =
  FunBind [ Match noLoc (name "runTest") args Nothing (UnGuardedRhs rhs) Nothing ]
  where pvarn n    = pvar $ name n
        varn n     = Var . UnQual $ name n
        args       = [PTuple Boxed [pvarn "s"]]
        emptyVec p = vExp $ if isAbs p then emptyVec2DFn else emptyVecFn
        -- turn buffers into empty vectors
        bufs       = [ emptyVec p | p <- pids ci, _ <- tyMap ci ]
        -- runState s ... plist []
        rs_app     = appFun (varn runState)
                            ((varn "s") : bufs ++ [varn "sched", emptyListCon])
        -- let l = runState ... in ...
        rhs = Do [ Generator noLoc (pvarn "sched") schedGen
                 , Qualifier (metaFunction "return" [retExp])
                 ]
        schedGen = metaFunction "generate"
                   [ metaFunction "vectorOf"
                     [ intE 500, metaFunction "oneof" [listE [ mkPid p | p <- pids ci ]] ]
                   ]
        mkPid p = if isAbs p then 
                    fmap_syn (pidCons p)
                             (arbRange (intE 0) (pidChoose p))
                  else
                    metaFunction "return" [pidCons p]
        pidChoose p = metaFunction (pidBound p) [vExp "s"]
        pidCons p   = Con . UnQual $ name (pidConstructor p) 
        retExp      = tuple [vExp "s", rs_app]
                         -- ret_exp
        -- -- (reverse l, sched)
        -- retExp    = Tuple Boxed [ cons (vExp "s") (app (varn "reverse") (varn "l"))
        --                         , varn "sched"
        --                         ]


-- ### Arbitrary instances ##################################################

-- instance Arbitrary State where
--         arbitrary
--           = State <$> .. <*> ...

arbFn :: String
arbFn  = "arbitrary"

arbPos :: Exp    
arbPos = fmap_syn (vExp "getPositive") (vExp arbFn)

arbZero :: Exp
arbZero = metaFunction "return" [intE 0]

arbRange :: Exp -> Exp -> Exp
arbRange e1 e2 = metaFunction "choose"
                 [App (App (tuple_con Boxed 1) e1) (infixApp e2 opMinus (intE 1))]

arbNull :: Exp
arbNull = metaFunction "return" [vExp nullCons]

arbEmptyMap :: Exp
arbEmptyMap = metaFunction "return" [vExp "emptyMap"]

arbitraryStateDecl    :: (Data a, Identable a)
                      => ConfigInfo a -> Decl
arbitraryStateDecl ci =  InstDecl noLoc Nothing [] [] tc_name [tv_name] [InsDecl (FunBind [arb])]
  where tc_name   = UnQual $ name "Arbitrary"
        tv_name   = TyVar $ name stateRecordCons
        arb       = Match noLoc (name "arbitrary") [] Nothing genExp Nothing
        genExp    = UnGuardedRhs $ Do (bs ++ [retState])
        retState  = Qualifier (metaFunction "return" [recExp])
        recExp    = RecConstr (UnQual (name stateRecordCons)) [FieldWildcard]
        bs        = withStateFields ci SFV { combine = concat
                                           , absF = absArb
                                           , pcF = arbPC
                                           , ptrF = arbPtr
                                           , valF = arbVal
                                           , intF = arbInt
                                           , globF = arbGlobVal
                                           , globIntF = arbGlob
                                           }
        bind v e  = Generator noLoc (pvar (name v)) e
        bindBound v e = case setBound ci (S v) of
                          Just (Unknown _ (V n)) ->
                            bind v (metaFunction "return" [vExp n])
                          Just (Known _ i) ->
                            bind v (metaFunction "return" [intE (toInteger i)]) 
                          _                ->
                            bind v e
        absArb p b pc blk = [ bindBound b arbPos
                            , bind pc (singletonMap (intE 0) (vExp b))
                            , if initBlocked p then
                                bind blk (metaFunction "return" [vExp b])
                              else
                                bind blk arbZero
                            ]
        initBlocked p  = case snd (pidProc ci p) of
                           Recv{} -> True
                           _      -> False
        
        arbPC p v      = arbInt p v
        arbPtr p rd wr = arbInt p rd ++ arbInt p wr
        arbInt p v     = [bind v $ if isAbs p then arbEmptyMap else arbZero]
        arbVal p v     = [bind v $ if isAbs p then arbEmptyMap else arbNull]
        arbGlobVal v   = [bind v arbNull]
        arbGlob v      = [bindBound v arbPos | v `notElem` absPidSets ]
        absPidSets     = [ setName s | PAbs _ s <- fst <$> cProcs (config ci) ]
        singletonMap k v = metaFunction "return"
                             [metaFunction "SymMap.singleton"
                               [k, infixApp v opMinus (intE 1)]]
        -- abs
        -- gen_exp   = foldl' (\e v -> fapp_syn e v)
        --                    (fmap_syn (Con $ UnQual $ name stateRecordCons) vh)
        --                    vt
        -- arb_rhs   = UnGuardedRhs $ genExp

-- instance Arbitrary p1 => Arbitrary (Pid_pre p1) where
--         arbitrary = oneof [return PIDR0, PIDR2 <$> arbitrary, ...]
arbitraryPidPreDecl    :: ConfigInfo a -> Decl
arbitraryPidPreDecl ci =
  InstDecl noLoc Nothing [] ctx tc_name [tv_name] [InsDecl (FunBind [arb])]
  where
        -- possible context class
        ctx     = [ClassA tc_name [TyVar v] | v <- pid_vars]
        tc_name = UnQual $ name "Arbitrary"
        -- Pid_pre p1 ...
        tv_name = TyParen (foldl' TyApp (TyVar $ name pidPre) [TyVar v | v <- pid_vars])
        arb     = Match noLoc (name "arbitrary") [] Nothing arb_rhs Nothing
        arb_rhs = UnGuardedRhs (app (var' "oneof") (listE pid_ts))
        pid_ts  = Prelude.map pidGen ts

        pidName p = Con . UnQual $ name (pidConstructor p)
        pidGen (p, _) = if isAbs p
                          then fmap_syn (pidName p) (var' "arbitrary")
                          else app (var' "return") (pidName p)

        var' s  = var $ name s
        pid_vars = [ t | (p, t) <- ts, isAbs p  ]
        ts       = [ (p, mkTy t) | p <- pids ci | t <- [0..] ]
        mkTy     = name . ("p" ++) . show
-- ### Aeson (FromJSON, ToJSON) instances ##################################################

-- instance FromJSON State where
--   parseJSON (Object s) = State <$>
--                          s .: "pidR0Pc" <*>
--                          ...
--                          s .: "x_3"
--   parseJSON _            = mzero
stateFromJSONDecl    :: ConfigInfo a -> Decl
stateFromJSONDecl ci =
  InstDecl noLoc Nothing [] [] tc_name [tv_name] [InsDecl (FunBind [fr, fr_err])]
  where
        fr = Match noLoc (name "parseJSON") fr_arg Nothing (UnGuardedRhs rhs) Nothing
        -- State <$> s .: <first var> <*> s .: <second var> <*> ...
        -- rhs = foldl' (\e s -> fapp_syn e s) rhs' ns'
        rhs = Do (bs ++ [Qualifier ret])
        ret = metaFunction "return" [RecConstr (qname stateRecordCons) [FieldWildcard]]
        varParser n = Generator noLoc (pvarn n)
                      (infix_syn ".:" (var $ name "s") (Lit $ String n))
        -- the names of the arguments in the state
        bs = withStateFields ci SFV { combine = concat
                                    , absF = absFs
                                    , pcF = pcFs
                                    , ptrF = ptrFs
                                    , valF = field
                                    , intF = field
                                    , globF = glob
                                    , globIntF = glob
                                    }
        absFs _ x y z = [varParser x, varParser y, varParser z]
        pcFs _ f      = [varParser f]
        ptrFs _ f1 f2 = [varParser f1, varParser f2]
        field _ f     = [varParser f]
        glob f        = [varParser f | f `notElem` absPidSets]
        absPidSets    = [ setName s | PAbs _ s <- fst <$> cProcs (config ci) ]


        -- parseJSON _ = mzero
        fr_err  = Match noLoc (name "parseJSON") [PWildCard] Nothing rhs_err Nothing
        rhs_err = UnGuardedRhs . vExp $ "mzero"

        tc_name = UnQual $ name "FromJSON"
        tv_name = TyVar $ name stateRecordCons
        qname n = UnQual $ name n
        pvarn n = H.PVar $ name n
        fr_arg = [PApp (qname "Object") [pvarn "s"]]


-- instance ToJSON State where
--   toJSON State{..} = object [ "pidR0Pc"    .= pidR0Pc
--                             , ...
--                             , "x_3"        .= x_3        ]
stateToJSONDecl    :: ConfigInfo a -> Decl
stateToJSONDecl ci =
  InstDecl noLoc Nothing [] [] tc_name [tv_name] [InsDecl (FunBind [to])]
  where
        to = Match noLoc (name "toJSON") to_arg Nothing (UnGuardedRhs rhs) Nothing

        -- = object ["<var 1>" .= <var 1>, ..., "<var n>" .= <var n>]
        rhs = app (var $ name "object") (listE exps)

        -- ["<var 1>" .= <var 1>, ..., "<var n>" .= <var n>]
        -- exps = map (\(n,_) -> infix_syn ".=" (Lit $ String n) (var $ name n))
        --            (stateVarsNTList ci)
        enc v = infix_syn ".=" (Lit $ String v) (var $ name v)
        exps =  withStateFields ci SFV { combine = concat
                                       , absF = absFs
                                       , pcF = pcFs
                                       , ptrF = ptrFs
                                       , valF = field
                                       , intF = field
                                       , globF = glob
                                       , globIntF = glob
                                       }
        absFs _ x y z = [enc x, enc y, enc z]
        pcFs _ f      = [enc f]
        ptrFs _ f1 f2 = [enc f1, enc f2]
        field _ f     = [enc f]
        glob f        = [enc f | f `notElem` absPidSets]
        absPidSets    = [ setName s | PAbs _ s <- fst <$> cProcs (config ci) ]

        -- parseJSON _ = mzero
        tc_name = UnQual $ name "ToJSON"
        tv_name = TyVar $ name stateRecordCons
        qname n = UnQual $ name n
        -- State{..}
        to_arg = [PRec (qname "State") [PFieldWildcard]]

-- instance (FromJSON p1) => FromJSON (Pid_pre p1) where
--   parseJSON (Object o) = case toList o of
--     [(k,v)] | k == "PIDR0" -> return PIDR0
--             | k == "PIDR2" -> PIDR2 <$> parseJSON v
--   parseJSON _ = mzero
pidFromJSONDecl    :: ConfigInfo a -> Decl
pidFromJSONDecl ci =
  InstDecl noLoc Nothing [] ctx tc_name [tv_name] [InsDecl (FunBind [fr, fr_err])]
  where
        fr     = Match noLoc (name "parseJSON") fr_arg Nothing (UnGuardedRhs rhs) Nothing
        fr_arg = [PApp (qname "Object") [pvarn "o"]]

        -- case H.toList o of ...
        rhs = H.Case (app (qvar (ModuleName "H") (name "toList")) (var' "o")) alts

        -- [(key,value)]
        alts     = [Alt noLoc case_pat case_rhs Nothing]

        -- [(k,v)] | ...
        case_pat = PList [PTuple Boxed [pvar' "k", pvar' "v"]]
        -- ... | k = PIDR0 -> return PIDR0 ...
        case_rhs = GuardedRhss guards

        guards   = [ GuardedRhs noLoc [g_stmt p] (g_exp p) | p <- pids ci ]
        g_stmt p = Qualifier $ infix_syn "==" (var' "k")
                                              (Lit $ String (pidConstructor p))
        g_exp p = let pidCon = Con . UnQual $ name (pidConstructor p)
                  in if isAbs p
                     then fmap_syn pidCon (app (var' "parseJSON") (var' "v"))
                     else app (var' "return") pidCon

        -- parseJSON _ = mzero
        fr_err  = Match noLoc (name "parseJSON") [PWildCard] Nothing rhs_err Nothing
        rhs_err = UnGuardedRhs . var . name $ "mzero"

        -- possible context class
        ctx     = [ClassA tc_name [TyVar v] | v <- pid_vars]
        tc_name = UnQual $ name "FromJSON"
        -- Pid_pre p1 ...
        tv_name = TyParen (foldl' TyApp (TyVar $ name pidPre) [TyVar v | v <- pid_vars])

        var' s  = var $ name s
        pvar' s = pvar $ name s
        qname n = UnQual $ name n
        pvarn n = H.PVar $ name n

        pid_vars = [ t | (p, t) <- ts, isAbs p  ]
        ts       = [ (p, mkTy t) | p <- pids ci | t <- [0..] ]
        mkTy     = name . ("p" ++) . show

-- instance (ToJSON p1) => ToJSON (Pid_pre p1) where
--   toJSON PIDR0       = object [ "PIDR0" .= Null ]
--   toJSON (PIDR2 pid) = object [ "PIDR2" .= toJSON pid ]
pidToJSONDecl    :: ConfigInfo a -> Decl
pidToJSONDecl ci =
  InstDecl noLoc Nothing [] ctx tc_name [tv_name] [InsDecl (FunBind tos)]
  where
        tos = [Match noLoc
                     (name "toJSON")
                     [to_arg p]
                     Nothing
                     (UnGuardedRhs (to_rhs p))
                     Nothing | p <- pids ci]

        to_arg p = if isAbs p
                   then PParen $ PApp (qname (pidConstructor p)) [pvarn "pid"]
                   else PApp (qname (pidConstructor p)) []

        to_rhs p = app (var' "object")
                       (listE [infix_syn ".="
                                         (Lit $ String (pidConstructor p))
                                         (if isAbs p
                                             then app (var' "toJSON") (var' "pid")
                                             else Con $ qname "Null")])

        -- possible context class
        ctx     = [ClassA tc_name [TyVar v] | v <- pid_vars]
        tc_name = UnQual $ name "ToJSON"
        -- Pid_pre p1 ...
        tv_name = TyParen (foldl' TyApp (TyVar $ name pidPre) [TyVar v | v <- pid_vars])

        var' s  = var $ name s
        qname n = UnQual $ name n
        pvarn n = H.PVar $ name n

        pid_vars = [ t | (p, t) <- ts, isAbs p  ]
        ts       = [ (p, mkTy t) | p <- pids ci | t <- [0..] ]
        mkTy     = name . ("p" ++) . show

-- ### "Static" functions to be included ##################################################
qcDefsStr n = unlines [ "fn = \"states.json\""
                      , "sample_size = " ++ show n
                      , "type Run = [(State, Pid)]"
                      , "type QCResult = (State, Either Run Run)"
                      ]

qcMainStr="main :: IO () \n\
\main = do b <- doesFileExist fn \n\
\          when b (removeFile fn) \n\
\\n\
\          inputs  <- generate $ vector sample_size :: IO [State] \n\
\          results <- mapM runTest inputs \n\
\          C.writeFile fn (fromString \"var states =\\n\")\n\
\          C.appendFile fn (encodePretty $ toJSON results) \n\
\          when (any (isLeft . snd) results) exitFailure\n\
\          exitSuccess\n\
\\n\
\      --  bs <- C.readFile fn \n\
\      --  let Just l = decode bs :: Maybe [QCResult] \n\
\      --  Prelude.putStrLn (\"Successfull runs: \" ++ (show $ length l)) \n"


arbValStr = "instance (Arbitrary a) => Arbitrary (Val a) where \n\
\  arbitrary = oneof [ return VUnit \n\
\                    , return VUnInit \n\
\                    , VInt    <$> arbitrary \n\
\                    , VString <$> arbitrary \n\
\                    , VPid    <$> arbitrary \n\
\                    , VInL    <$> arbitrary \n\
\                    , VInR    <$> arbitrary \n\
\                    , VPair   <$> arbitrary <*> arbitrary ]\n"

arbVecStr="instance (Arbitrary a) => Arbitrary (Vec a) where \n\
\   arbitrary = do a <- arbitrary \n\
\                  return $ mkVec a\n"
