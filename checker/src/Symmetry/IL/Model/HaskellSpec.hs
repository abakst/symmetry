{-# Language ParallelListComp #-}
{-# LANGUAGE ViewPatterns #-}
module Symmetry.IL.Model.HaskellSpec where

import           Data.Char
import           Data.Generics
import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as S
import qualified Data.Map.Strict as Map
import           Data.List
import           Data.Maybe
import           Language.Haskell.Exts.Pretty
import           Language.Haskell.Exts.Syntax hiding (Stmt)
import           Language.Haskell.Exts.SrcLoc
import           Language.Haskell.Exts.Build
import           Language.Fixpoint.Types as F
import           Text.Printf

import Symmetry.IL.AST as AST
import Symmetry.IL.ConfigInfo
import Symmetry.IL.Model
import Symmetry.IL.Model.HaskellDefs

instance Symbolic Name where
  symbol (Ident x) = symbol x

pp :: Pretty a => a -> String
pp = prettyPrint                     

eRange :: F.Expr -> F.Expr -> F.Expr -> F.Expr
eRange v elow ehigh
  = pAnd [PAtom Le elow v, PAtom Lt v ehigh]

eRangeI :: F.Expr -> F.Expr -> F.Expr -> F.Expr
eRangeI v elow ehigh
  = pAnd [PAtom Le elow v, PAtom Le v ehigh]

eEq :: F.Expr -> F.Expr -> F.Expr                       
eEq e1 e2 = PAtom Eq e1 e2

eLe :: F.Expr -> F.Expr -> F.Expr            
eLe e1 e2 = PAtom Le e1 e2            

eDec :: F.Expr -> F.Expr
eDec e = EBin Minus e (F.expr (1 :: Int))

ePlus :: F.Expr -> F.Expr -> F.Expr
ePlus e1 e2 = EBin Plus e1 e2

eILVar :: Var -> F.Expr            
eILVar (V v)  = eVar v
eILVar (GV v) = eVar v

eZero :: F.Expr
eZero = F.expr (0 :: Int)

eEqZero :: F.Expr -> F.Expr                       
eEqZero e = eEq e eZero

eApp :: Symbolic a => a -> [F.Expr] -> F.Expr            
eApp f = EApp (dummyLoc $ symbol f)

pidToExpr :: Pid -> F.Expr        
pidToExpr p@(PConc _) = eVar $ pid p        
pidToExpr p@(PAbs (V v) (S s)) = eApp (pid p) [eVar $ pidIdx p]

eReadState :: (Symbolic a, Symbolic b) => a -> b -> F.Expr                        
eReadState s f 
  = eApp (symbol f) [eVar s]

eReadMap e k
  = eApp "Map_select" {- mapGetSpecString -} [e, k]

eRdPtr, eWrPtr :: Symbolic a => ConfigInfo Int -> Pid -> ILType -> a -> F.Expr
eRdPtr ci p t s
  = eReadState s (ptrR ci p t)
eWrPtr ci p t s
  = eReadState s (ptrW ci p t)

initOfPid :: ConfigInfo Int -> Process Int -> F.Expr
initOfPid ci (p@(PAbs _ (S s)), stmt)
  = pAnd preds 
  where
    preds    = [ counterInit
               , unfoldInit
               , eRange (eReadState st eK)
                 eZero (eReadState st (pidBound p))
               , eEq counterSum setSize
               ] ++ counterInits
    st       = "v"
    eK       = pidUnfold p
    counterInit  = eEq setSize (readCtr 0)
    unfoldInit   = eEq eZero (eReadMap (eReadState st (pc p)) (eReadState st eK))
    setSize      = eDec (eReadState st (pidBound p))
    counterSum   = foldl' (\e i -> ePlus e (readCtr i)) (readCtr (-1)) stmts
    counterInits = (\i -> eEq eZero (readCtr i)) <$> filter (/= 0) ((-1) : stmts)
    counterBounds= (\i -> eLe eZero (readCtr i)) <$> filter (/= 0) stmts

    readCtr :: Int -> F.Expr
    readCtr i  = eReadMap (eReadState st (pidPcCounter p)) (fixE i)

    fixE i     = if i < 0 then ECst (F.expr i) FInt else F.expr i
    stmts :: [Int]
    stmts = everything (++) (mkQ [] go) stmt
    go s = [annot s]

initOfPid ci (p@(PConc _), stmt)
  = pAnd (pcEqZero :
          concat [[ rdEqZero t, rdGeZero t
                  , wrEqZero t, wrGeZero t
                  , rdLeWr t               ] | t <- fst <$> tyMap ci ])
    where
      s           = "v"
      pcEqZero    = eEq (eReadState s (pc p)) (F.expr initStmt)
      rdEqZero t  = eEqZero (eRdPtr ci p t s)
      rdGeZero t  = eLe eZero (eRdPtr ci p t s)
      wrEqZero t  = eEqZero (eWrPtr ci p t s)
      wrGeZero t  = eLe eZero (eWrPtr ci p t s)
      rdLeWr t    = eLe (eRdPtr ci p t s) (eWrPtr ci p t s)
      initStmt    = firstNonBlock stmt
      firstNonBlock SBlock { blkBody = bs } = annot (head bs)
      firstNonBlock s                       = annot s

schedExprOfPid :: ConfigInfo Int -> Pid -> Symbol -> F.Expr
schedExprOfPid ci p@(PAbs v (S s)) state
  = subst1 (pAnd ([pcEqZero, idxBounds] ++
                  concat [[rdEqZero t, wrEqZero t, wrGtZero t] | t <- fst <$> tyMap ci]))
           (symbol (pidIdx p), eVar "v")
    where
      idxBounds  = eRange (eVar "v") (F.expr (0 :: Int)) (eReadState state s)
      pcEqZero   = eEqZero (eReadMap (eReadState state (pc p)) (eILVar v))
      rdEqZero t = eRangeI eZero (eReadMap (eRdPtr ci p t state) (eILVar v)) (eReadMap (eWrPtr ci p t state) (eILVar v))
      wrEqZero t = eEqZero (eReadMap (eWrPtr ci p t state) (eILVar v))
      wrGtZero t = eLe eZero (eReadMap (eWrPtr ci p t state) (eILVar v))

schedExprsOfConfig :: ConfigInfo Int -> Symbol -> [F.Expr]
schedExprsOfConfig ci s
  = go <$> filter isAbs (fst <$> ps)
  where
    m    = tyMap ci
    ps   = cProcs (config ci)
    go p = schedExprOfPid ci p s
           
predToString :: F.Expr -> String
predToString = show . pprint

lhSpec :: String -> String
lhSpec x = "{-@\n" ++ x ++ "\n@-}"

specBind :: String -> String -> String
specBind x s = x ++ " :: " ++ s

specFmt :: String
specFmt = "{-@ assume %s :: {v:%s | %s} @-}" 

printSpec :: String -> String -> F.Expr -> String
printSpec x t p = printf specFmt x t (predToString p)

initStateReft :: F.Expr -> String                  
initStateReft p
  = printSpec initState stateRecordCons p

initSchedReft :: (Symbol -> [F.Expr]) -> String
initSchedReft p
  = printf "{-@ assume %s :: %s:State -> [%s %s] @-}"
      initSched
      initState
      pidPre
      (unwords args)
    where
      args = printf "{v:Int | %s}" . predToString
             <$> p (symbol initState)

nonDetSpec :: String    
nonDetSpec
  = printf "{-@ %s :: %s -> {v:Int | true} @-}" nondet (pp schedType)

measuresOfConfig :: Config Int -> String
measuresOfConfig Config { cProcs = ps }
  = unlines [ printf "{-@ measure %s @-}" (pidInj p) | (p, _) <- ps]

valMeasures :: String
valMeasures
  = unlines [ printf "{-@ measure %s @-}" (valInj v) | v <- valCons ]

builtinSpec :: [String]
builtinSpec = [nonDetSpec]

-- pidSpecString  Config { cProcs = ps }
--   = case absPs of
--       [] -> printf "{-@ data %s = %s @-}" pidTyString cstrs
--       _  -> printf "{-@ data %s %s = %s @-}" pidTyString cstrs
--     where
--       (absPs, concPs) = partition isAbs (fst <$> ps)
--       cstrs     = intercalate " | " ((go <$> concPs) ++ (goAbs <$> absPs))
--       go p@(PConc _)  = (pid p)
--       goAbs p@(PAbs _ _) = printf "%s { pidIdx :: Int }" (unName (pidNameOfPid p))

-- recQuals (HsDataDecl _ _ _ _ [c] _)
--   = unlines $ recQualsCon c
--   where
--     printTy (HsUnBangedTy (HsTyTuple _)) = "a"
--     printTy t             = pp t
--     recQualsCon (HsRecDecl _ _ fs)
--       = concatMap recQualField fs
--     recQualField ([f], t)
--       = [ printf "{-@ qualif Deref_%s(v:%s, x:%s): v = %s x @-}"
--             (unName f) (printTy t) stateTyString (unName f)
--         , printf "{-@ qualif Eq_%s(v:%s, x:%s): %s v = %s x @-}"
--             (unName f) stateTyString stateTyString (unName f) (unName f)
--         ]

-- stateRecordDefSpec :: Config Int -> HsDecl -> String
-- stateRecordDefSpec Config { cProcs = cs } (HsDataDecl _ _ _ _ [c] _)
--   = printf "data State <%s> = State { %s }"
--            (intercalate ", " ((dom <$> ps) ++ (rng <$> ps)))
--            (intercalate ", " (declFields c)) -- fields
--   where
--     dom p = printf "dom%s :: Int -> Prop" (toLower <$> pidString p)
--     rng p = printf "rng%s :: Int -> Val -> Prop" (toLower <$> pidString p)
--     ps = fst <$> cs
--     declFields (HsRecDecl _ _ fs) = declField <$> fs
--     declField ([f], t)
--       -- | t == vecType valType   = printf "%s <%s, %s> :: %s" (pp f) (dom p) (rng p)
--       -- | t == vec2DType valType = undefined
--       | otherwise = printf "%s :: %s" (pp f) (pp t)

---------------------
-- Type Declarations
---------------------
intType  = TyCon (UnQual (name "Int"))
mapTyCon = TyCon (UnQual (name "Map_t"))

mapType k v = TyApp (TyApp mapTyCon k) v

stateRecord :: [([Name], Type)] -> QualConDecl
stateRecord fs
  = QualConDecl noLoc [] [] (RecDecl (name stateRecordCons) fs)
  
stateDecl :: ConfigInfo Int
          -> ([Decl], String)
stateDecl ci
  = ([dataDecl], specStrings)
  where
    dataDecl     = DataDecl noLoc DataType [] (name stateRecordCons) [] [stateRecord fs] []
    specStrings  = unlines [ dataReft
                           , ""
                           , recQuals
                           , ""
                           ]

    dataReft     = printf "{-@ %s @-}" (pp dataDecl)
    fs = pcFs ++ ptrFs ++ valVarFs ++ intVarFs ++ absFs
    absFs    = concat [ [mkBound p, mkCounter p, mkUnfold p] | p <- pids ci, isAbs p ]
    pcFs     = [ mkPC p (pc p) | p <- pids ci ]
    ptrFs    = [ mkInt p (ptrR ci p t) | p <- pids ci, t <- fst <$> tyMap ci] ++
               [ mkInt p (ptrW ci p t) | p <- pids ci, t <- fst <$> tyMap ci]
    valVarFs = [ mkVal p v | (p, v) <- valVars (stateVars ci) ]
    intVarFs = [ mkInt p v | (p, v) <- intVars (stateVars ci) ]

    mkUnfold p  = ([name $ pidUnfold p], intType)
    mkBound p   = ([name $ pidBound p], intType)
    mkCounter p = ([name $ pcCounter p], mapType intType intType)
    recQuals = unlines [ mkDeref f t ++ "\n" ++ mkEq f | ([f], t) <- fs ]

    mkDeref f t = printf "{-@ qualif Deref_%s(v:%s, w:%s): v = %s w @-}"
                          (pp f) (pp t) stateRecordCons (pp f) 
    mkEq f = printf "{-@ qualif Eq_%s(v:%s, w:%s ): %s v = %s w @-}"
                     (pp f) stateRecordCons stateRecordCons (pp f) (pp f)
    mkPC  = liftMap intType
    mkVal = liftMap (valHType ci)
    mkInt = liftMap intType
    liftMap t p v = ([name v], if isAbs p then mapType intType t else t)

valHType :: ConfigInfo Int -> Type
valHType ci = TyApp (TyCon (UnQual (name valType)))
                    (pidPreApp ci)

pidPreApp ci
  = foldl' TyApp (TyCon . UnQual $ name pidPre) pidPreArgs
  where
    pidPreArgs :: [Type]
    pidPreArgs = const intType <$> filter isAbs (pids ci)

pidDecl :: ConfigInfo Int
        -> [Decl]
pidDecl ci
  = [ DataDecl noLoc DataType [] (name pidPre) tvbinds cons []
    , TypeDecl noLoc (name pidType) [] (pidPreApp ci)
    ] ++
    (pidFn <$> pids ci)
  where
    mkPidCons  pt     = QualConDecl noLoc [] [] (mkPidCons' pt)
    mkPidCons' (p, t) = if isAbs p then
                          ConDecl (name (pidConstructor p)) [TyVar t]
                        else
                          ConDecl (name (pidConstructor p)) []
                          

    cons        = mkPidCons <$> ts
    tvbinds     = [ UnkindedVar t | (p, t) <- ts, isAbs p  ]
    ts          = [ (p, mkTy t) | p <- pids ci | t <- [0..] ]
    mkTy        = name . ("p" ++) . show

pidFn :: Pid -> Decl
pidFn p
  = FunBind [ Match noLoc (name $ pidInj p) [pidPattern p] Nothing truerhs Nothing
            , Match noLoc (name $ pidInj p) [PWildCard] Nothing falserhs Nothing
            ]
  where
    truerhs = UnGuardedRhs (var (sym "True"))
    falserhs = UnGuardedRhs (var (sym "False"))

-- stateRecordSpec :: ConfigInfo Int -> String
-- stateRecordSpec ci
--   = unlines [ printf "{-@ %s @-}" st
--             , measuresOfConfig (config ci)
--             , valMeasures
--             , recQuals st
--             ]
--     where
--       st = stateDecl ci

-- valTypeSpec :: String
-- valTypeSpec = printf "{-@ %s @-}" (pp valDecl)

initSpecOfConfig :: ConfigInfo Int -> String               
initSpecOfConfig ci
  = unlines [ initStateReft concExpr
            , initSchedReft schedExprs
            , stateSpec
            , unlines (pp <$> stateDecls)
            , ""
            , unlines (pp <$> pidDecls)
            , ""
            , measuresOfConfig (config ci)
--            , stateRecordSpec ci
--            , valTypeSpec
            ]
     -- ++ qualsOfConfig ci
    
    where
      concExpr   = pAnd  ((initOfPid ci <$> cProcs (config ci)) ++
                          [ eEqZero (eReadState (symbol "v") (symbol v))
                          | V v <- iters ])
      iters      = everything (++) (mkQ [] goVars) (cProcs (config ci))
      goVars :: Stmt Int -> [Var]
      goVars SIter {iterVar = v} = [v]
      goVars _                   = []
      schedExprs = schedExprsOfConfig ci
      (stateDecls, stateSpec) = stateDecl ci
      pidDecls = pidDecl ci

recvTy :: [Stmt Int] -> [ILType]
recvTy = everything (++) (mkQ [] go)
  where
    go :: Stmt Int -> [ILType]
    go (SRecv (t, _) _) = [t]
    go _                 = []

-- Qualifiers                           
{-
pc = 0 => f x = y
-}
{-
data Context = Iter Var Set
             | Loop Var
               deriving (Eq, Ord, Show)

qualsOfConfig :: ConfigInfo Int -> String
qualsOfConfig ci 
  = unlines $ concatMap (qualsOfProc ci) (cProcs (config ci))

qualsOfProc ci (p, s)
  = qualsOfStmt ci [] p rds [wrs] s
    where
      rds = Map.fromList ((const 0<$>) <$> tyMap ci)
      wrs = Map.fromList (zip (pids ci) (repeat rds))

qualsOfStmt :: ConfigInfo Int
            -> [Context] -- stack of contexts
            -> Pid -- whose stmt
            -> Map.Map ILType Int             -- recvs
            -> [Map.Map Pid (Map.Map ILType Int)] -- send alternatives
            -> Stmt Int
            -> [String]
qualsOfStmt ci ctxt p rds wrs s@SSend{ sndPid = q, sndMsg = (t, _) }
  = renderQual ci ctxt p rds wrs (annot s) ++
    concatMap (qualsOfStmt ci ctxt p rds (incWrTy q t wrs)) (childStmts ci p s)
qualsOfStmt ci ctxt p rds wrs s@SRecv{ rcvMsg = (t, _) }
  = renderQual ci ctxt p rds wrs (annot s) ++
    concatMap (qualsOfStmt ci ctxt p (incRdTy t rds) wrs) (childStmts ci p s)
qualsOfStmt ci ctxt p rds wrs s@SIter{ iterBody = b }
  = renderQual ci ctxt p rds wrs (annot s) ++
    qualsOfStmt ci' ctxt' p rds wrs b ++
                -- This isn't right:
    concatMap (qualsOfStmt ci' ctxt' p rds wrs) (childStmts ci' p s)
  where
    ctxt' = Iter (iterVar s) (iterSet s) : ctxt
    ci'   = ci { cfg = upd <$> cfg ci }
    upd (p', m) | p == p'   = (p, M.map (filter ((/= (annot s)) . annot)) m)
                | otherwise = (p', m)
qualsOfStmt ci ctxt p rds wrs s
  = renderQual ci ctxt p rds wrs (annot s) ++
    concatMap (qualsOfStmt ci ctxt p rds wrs) (childStmts ci p s)
-- qualsOfStmt rds wrs cfg s
--   = [printf "PC = %s => READ = %s && SEND = %s" (show (annot s)) (showpp rds) (showpp wrs)] ++
--     concatMap (qualsOfStmt rds wrs cfg) (M.findWithDefault [] (annot s) cfg)
renderQual ci ctxt p rds wrs i
  = [ printf "{-@ qualif Rd(v:State): (%s v) = %d => %s @-}"
             (pc p) i (renderRds ci p rds) ] ++
    [ printf "{-@ qualif Wr(v:State): (%s v) = %d => %s @-}"
             (pc p) i (renderWrs ci ctxt wrs) ]

renderRds' :: Map.Map ILType [(ILExpr,Int)] -> [F.Expr]
renderRds' m = go <$> Map.toList m
  where
    go (t, n) = undefined

renderRds :: ConfigInfo Int -> Pid -> Map.Map ILType Int -> String
renderRds ci p m = Map.foldrWithKey go "" m
  where
    go t n "" = printf "(%s v) = %d" (ptrR ci p t) n
    go t n s  = printf "(%s v) = %d && %s" (ptrR ci p t) n s

renderWrs :: ConfigInfo Int -> [Context] -> [Map.Map Pid (Map.Map ILType Int)] -> String
renderWrs ci ctxt ms
  = unlines $ concat [renderOneWr <$> Map.toList m | m <- ms]
  where
    renderOneWr (p, tm) = Map.foldrWithKey (go p) "" tm
    go p t n "" = printf "(%s v) = %d"       (ptrW ci p t) n
    go p t n s  = printf "(%s v) = %d && %s" (ptrW ci p t) n n s

iterContext ctxt v
  = length $ [ c | c@(Iter v' _) <- ctxt, v == v' ]

incRdTy t m = Map.alter go t m
  where
    go Nothing  = Just 1
    go (Just n) = Just (n + 1)

incWrTy :: ILExpr
        -> ILType
        -> [Map.Map Pid (Map.Map ILType Int)]
        -> [Map.Map Pid (Map.Map ILType Int)]
incWrTy (EPid p) t ms
  = Map.alter (Map.alter go t <$>) p <$> ms
  where
    go Nothing  = Just 1
    go (Just n) = Just (n + 1)
incWrTy (AST.EVar _) t ms
  = [ Map.alter (Map.alter go t <$>) q m | m <- ms, q <- Map.keys m ]
  where
    go Nothing  = Just 1
    go (Just n) = Just (n + 1)


childStmts :: ConfigInfo Int -> Pid -> Stmt Int -> [Stmt Int]
childStmts ci p (annot -> -1) = []
childStmts ci p s             = maybe [SSkip (-1)] id $ cfgNext ci p (annot s)
-}
