{-# LANGUAGE ViewPatterns #-}
module Symmetry.IL.Render.Horn.Spec where

import           Data.Char
import           Data.Generics
-- import           Data.Graph.Inductive.Graph hiding (prettyPrint)
-- import           Data.Graph.Inductive.Query.Dominators
-- import           Data.Graph.Inductive.PatriciaTree
-- import           Data.Graph.Inductive.NodeMap
import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as S
import qualified Data.Map.Strict as Map
import           Data.List
import           Data.Maybe
import           Language.Haskell.Syntax
import           Language.Fixpoint.Types as F
import           Language.Haskell.Pretty
import           Text.Printf

import Symmetry.IL.AST as AST
import Symmetry.IL.Render.Horn.Config
import Symmetry.IL.Render.Horn.Decls
import Symmetry.IL.Render.Horn.Types

instance Symbolic HsName where
  symbol (HsIdent x) = symbol x

eRange :: Expr -> Expr -> Expr -> Expr
eRange v elow ehigh
  = pAnd [PAtom Le elow v, PAtom Lt v ehigh]

eRangeI :: Expr -> Expr -> Expr -> Expr
eRangeI v elow ehigh
  = pAnd [PAtom Le elow v, PAtom Le v ehigh]

eEq :: Expr -> Expr -> Expr                       
eEq e1 e2 = PAtom Eq e1 e2

eLe :: Expr -> Expr -> Expr            
eLe e1 e2 = PAtom Le e1 e2            

eDec :: Expr -> Expr
eDec e = EBin Minus e (expr (1 :: Int))

ePlus :: Expr -> Expr -> Expr
ePlus e1 e2 = EBin Plus e1 e2

eILVar :: Var -> Expr            
eILVar (V v)  = eVar v
eILVar (GV v) = eVar v

eZero :: Expr
eZero = expr (0 :: Int)

eEqZero :: Expr -> Expr                       
eEqZero e = eEq e eZero

app :: Symbolic a => a -> [Expr] -> Expr            
app f = EApp (dummyLoc $ symbol f)

pidToExpr :: Pid -> Expr        
pidToExpr p@(PConc _) = eVar $ pidNameOfPid p        
pidToExpr p@(PAbs (V v) (S s)) = app (pidNameOfPid p) [eVar $ idxNameOfPid p]

eReadState :: (Symbolic a, Symbolic b) => a -> b -> Expr                        
eReadState s f 
  = app (symbol f) [eVar s]

ePtrKey :: Expr -> Expr -> Expr
ePtrKey p i = app ptrKeyTyName [p, i]

eReadMap e k
  = app mapGetSpecString [e, k]

eRdPtr, eWrPtr :: Symbolic a => a -> Integer -> Pid -> Expr
eRdPtr s t p    
  = eReadState s (pidRdPtrName t p)
eWrPtr s t p    
  = eReadState s (pidWrPtrName t p)

initOfPid :: TyMap -> Process Int -> Expr
initOfPid m (p@(PAbs _ (S s)), stmt)
  = pAnd preds 
  where
    preds    = [ counterInit
               , unfoldInit
               , eRange (eReadState st eK)
                 eZero (eReadState st (prefix stateString s))
               , eEq counterSum setSize
               ] ++ counterInits
    st       = "v"
    eK       = pidUnfoldName p
    counterInit  = eEq setSize (readCtr 0)
    unfoldInit   = eEq eZero (eReadMap (eReadState st (pcName p)) (eReadState st eK))
    setSize      = eDec (eReadState st (prefix stateString s))
    counterSum   = foldl' (\e i -> ePlus e (readCtr i)) (readCtr (-1)) stmts
    counterInits = (\i -> eEq eZero (readCtr i)) <$> filter (/= 0) ((-1) : stmts)
    counterBounds= (\i -> eLe eZero (readCtr i)) <$> filter (/= 0) stmts
    readCtr :: Int -> Expr
    readCtr i  = eReadMap (eReadState st (pidLocCounterName p)) (fixE i)
    fixE i     = if i < 0 then ECst (expr i) FInt else expr i
    stmts :: [Int]
    stmts = everything (++) (mkQ [] go) stmt
    go s = [annot s]

initOfPid m (p@(PConc _), stmt)
  = pAnd (pcEqZero :
          concat [[ rdEqZero t, rdGeZero t
                  , wrEqZero t, wrGeZero t
                  , rdLeWr t               ] | t <- snd <$> m ])
    where
      s           = "v"
      pcEqZero    = eEq (eReadState s (pcName p)) (expr initStmt)
      rdEqZero t  = eEqZero (eRdPtr s t p)
      rdGeZero t  = eLe eZero (eRdPtr s t p)
      wrEqZero t  = eEqZero (eWrPtr s t p)
      wrGeZero t  = eLe eZero (eWrPtr s t p)
      rdLeWr t    = eLe (eRdPtr s t p) (eWrPtr s t p)
      initStmt    = firstNonBlock stmt
      firstNonBlock SBlock { blkBody = bs } = annot (head bs)
      firstNonBlock s                       = annot s

schedExprOfPid :: TyMap -> Pid -> Symbol -> Expr
schedExprOfPid m p@(PAbs v (S s)) state
  = subst1 (pAnd ([pcEqZero, idxBounds] ++
                  concat [[rdEqZero t, wrEqZero t, wrGtZero t] | t <- snd <$> m]))
           (symbol (idxNameOfPid p), eVar "v")
    where
      idxBounds  = eRange (eVar "v") (expr (0 :: Int)) (eReadState state (prefix stateString s))
      pcEqZero   = eEqZero (eReadMap (eReadState state (pcName p)) (eILVar v))
      rdEqZero t = eRangeI eZero (eReadMap (eRdPtr state t p) (eILVar v)) (eReadMap (eWrPtr state t p) (eILVar v))
      wrEqZero t = eEqZero (eReadMap (eWrPtr state t p) (eILVar v))
      wrGtZero t = eLe eZero (eReadMap (eWrPtr state t p) (eILVar v))

schedExprsOfConfig :: ConfigInfo Int -> Symbol -> [Expr]
schedExprsOfConfig ci s
  = go <$> filter isAbs (fst <$> ps)
  where
    m    = tyMap ci
    ps   = cProcs (config ci)
    go p = schedExprOfPid m p s
           
predToString :: Expr -> String
predToString = show . pprint

lhSpec :: String -> String
lhSpec x = "{-@\n" ++ x ++ "\n@-}"

specBind :: String -> String -> String
specBind x s = x ++ " :: " ++ s

specFmt :: String
specFmt = "{-@ assume %s :: {v:%s | %s} @-}" 

printSpec :: String -> String -> Expr -> String
printSpec x t p = printf specFmt x t (predToString p)

initStateReft :: Expr -> String                  
initStateReft p
  = printSpec initialStateString stateTyString p

initSchedReft :: (Symbol -> [Expr]) -> String
initSchedReft p
  = printf "{-@ assume %s :: %s:State -> [%s %s] @-}"
      initialSchedString
      initialStateString
      prePidTyString
      (unwords args)
    where
      args = printf "{v:Int | %s}" . predToString
             <$> p (symbol initialStateString)

nonDetSpec :: String    
nonDetSpec
  = printf "{-@ %s :: %s -> {v:Int | true} @-}" nonDetString (prettyPrint schedTy)

measuresOfConfig :: Config Int -> String
measuresOfConfig Config { cProcs = ps }
  = unlines [ printf "{-@ measure %s @-}" (unName $ pidInjectiveName p) | (p, _) <- ps]

valMeasures :: String
valMeasures
  = unlines [ printf "{-@ measure %s @-}" (unName (valInjective n)) | (n, _) <- valConstructors ]

builtinSpec :: [String]
builtinSpec = [nonDetSpec]

pidSpecString  Config { cProcs = ps }
  = case absPs of
      [] -> printf "{-@ data %s = %s @-}" pidTyString cstrs
      _  -> printf "{-@ data %s %s = %s @-}" pidTyString cstrs
    where
      (absPs, concPs) = partition isAbs (fst <$> ps)
      cstrs     = intercalate " | " ((go <$> concPs) ++ (goAbs <$> absPs))
      go p@(PConc _)  = unName (pidNameOfPid p)
      goAbs p@(PAbs _ _) = printf "%s { pidIdx :: Int }" (unName (pidNameOfPid p))

recQuals (HsDataDecl _ _ _ _ [c] _)
  = unlines $ recQualsCon c
  where
    printTy (HsUnBangedTy (HsTyTuple _)) = "a"
    printTy t             = prettyPrint t
    recQualsCon (HsRecDecl _ _ fs)
      = concatMap recQualField fs
    recQualField ([f], t)
      = [ printf "{-@ qualif Deref_%s(v:%s, x:%s): v = %s x @-}"
            (unName f) (printTy t) stateTyString (unName f)
        , printf "{-@ qualif Eq_%s(v:%s, x:%s): %s v = %s x @-}"
            (unName f) stateTyString stateTyString (unName f) (unName f)
        ]

stateRecordDefSpec :: Config Int -> HsDecl -> String
stateRecordDefSpec Config { cProcs = cs } (HsDataDecl _ _ _ _ [c] _)
  = printf "data State <%s> = State { %s }"
           (intercalate ", " ((dom <$> ps) ++ (rng <$> ps)))
           (intercalate ", " (declFields c)) -- fields
  where
    dom p = printf "dom%s :: Int -> Prop" (toLower <$> pidString p)
    rng p = printf "rng%s :: Int -> Val -> Prop" (toLower <$> pidString p)
    ps = fst <$> cs
    declFields (HsRecDecl _ _ fs) = declField <$> fs
    declField ([f], t)
      -- | t == vecType valType   = printf "%s <%s, %s> :: %s" (prettyPrint f) (dom p) (rng p)
      -- | t == vec2DType valType = undefined
      | otherwise = printf "%s :: %s" (prettyPrint f) (prettyPrint t)

stateRecordSpec :: ConfigInfo Int -> String
stateRecordSpec ci
  = unlines [ printf "{-@ %s @-}" (stateRecordDefSpec (config ci) st)
            , measuresOfConfig (config ci)
            , valMeasures
            , recQuals st
            ]
    where
      st = stateTypeOfConfig ci

valTypeSpec :: String

removeDerivings (HsDataDecl srcloc ctx name names decls quals)
  = HsDataDecl srcloc ctx name names decls []

valTypeSpec = printf "{-@ %s @-}" (prettyPrint $ removeDerivings valDecl)

initSpecOfConfig :: ConfigInfo Int -> String               
initSpecOfConfig ci
  = unlines [ initStateReft concExpr
            , initSchedReft schedExprs
            , stateRecordSpec ci
            , valTypeSpec
            ]
     -- ++ qualsOfConfig ci
    
    where
      concExpr   = pAnd  ((initOfPid (tyMap ci) <$> cProcs (config ci)) ++
                          [ eEqZero (eReadState (symbol "v") (vSym v))
                          | V v <- iters ])
      vSym       = symbol . prefix stateString
      iters      = everything (++) (mkQ [] goVars) (cProcs (config ci))
      goVars :: Stmt Int -> [Var]
      goVars SIter {iterVar = v} = [v]
      goVars _                   = []
      schedExprs = schedExprsOfConfig ci

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
             pc i (renderRds ci p rds) ] ++
    [ printf "{-@ qualif Wr(v:State): (%s v) = %d => %s @-}"
             pc i (renderWrs ci ctxt wrs) ]
  where
    pc = pcString p

renderRds' :: Map.Map ILType [(ILExpr,Int)] -> [Expr]
renderRds' m = go <$> Map.toList m
  where
    go (t, n) = undefined

renderRds :: ConfigInfo Int -> Pid -> Map.Map ILType Int -> String
renderRds ci p m = Map.foldrWithKey go "" m
  where
    go t n "" = printf "(%s v) = %d" (pidRdPtrString (lookupTy ci t) p) n
    go t n s  = printf "(%s v) = %d && %s" (pidRdPtrString (lookupTy ci t) p) n s

renderWrs :: ConfigInfo Int -> [Context] -> [Map.Map Pid (Map.Map ILType Int)] -> String
renderWrs ci ctxt ms
  = unlines $ concat [renderOneWr <$> Map.toList m | m <- ms]
  where
    renderOneWr (p, tm) = Map.foldrWithKey (go p) "" tm
    go p t n "" = printf "(%s v) = %d"       (pidWrPtrString (lookupTy ci t) p) n
    go p t n s  = printf "(%s v) = %d && %s" (pidWrPtrString (lookupTy ci t) p) n s

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
