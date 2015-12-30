module Symmetry.IL.Render.Horn.Spec where

import           Data.Generics
import           Data.Graph.Inductive.Graph hiding (prettyPrint)
import           Data.Graph.Inductive.Query.Dominators
import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.NodeMap
import qualified Data.IntMap as M
import qualified Data.IntSet as S
import           Data.List
import           Data.Maybe
import           Language.Haskell.Syntax
import           Language.Fixpoint.Types  
import           Language.Fixpoint.PrettyPrint  
import           Language.Haskell.Pretty
import           Text.Printf

import Symmetry.IL.AST
import Symmetry.IL.Render.Horn.Decls
import Symmetry.IL.Render.Horn.Types

instance Symbolic HsName where
  symbol (HsIdent x) = symbol x

eRange :: Expr -> Expr -> Expr -> Pred
eRange v elow ehigh
  = pAnd [PAtom Le elow v, PAtom Lt v ehigh]

eRangeI :: Expr -> Expr -> Expr -> Pred
eRangeI v elow ehigh
  = pAnd [PAtom Le elow v, PAtom Le v ehigh]

eEq :: Expr -> Expr -> Pred                       
eEq e1 e2 = PAtom Eq e1 e2

eLe :: Expr -> Expr -> Pred            
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

eEqZero :: Expr -> Pred                       
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

initOfPid :: TyMap -> Process Int -> Pred
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

initOfPid m (p@(PConc _), _)
  = pAnd (pcEqZero :
          concat [[ rdEqZero t, rdGeZero t
                  , wrEqZero t, wrGeZero t
                  , rdLeWr t               ] | t <- snd <$> m ])
    where
      s           = "v"
      pcEqZero    = eEqZero (eReadState s (pcName p))
      rdEqZero t  = eEqZero (eRdPtr s t p)
      rdGeZero t  = eLe eZero (eRdPtr s t p)
      wrEqZero t  = eEqZero (eWrPtr s t p)
      wrGeZero t  = eLe eZero (eWrPtr s t p)
      rdLeWr t    = eLe (eRdPtr s t p) (eWrPtr s t p)

schedPredOfPid :: TyMap -> Pid -> Symbol -> Pred
schedPredOfPid m p@(PAbs v (S s)) state
  = subst1 (pAnd ([pcEqZero, idxBounds] ++
                  concat [[rdEqZero t, wrEqZero t, wrGtZero t] | t <- snd <$> m]))
           (symbol (idxNameOfPid p), eVar "v")
    where
      idxBounds  = eRange (eVar "v") (expr (0 :: Int)) (eReadState state (prefix stateString s))
      pcEqZero   = eEqZero (eReadMap (eReadState state (pcName p)) (eILVar v))
      rdEqZero t = eRangeI eZero (eReadMap (eRdPtr state t p) (eILVar v)) (eReadMap (eWrPtr state t p) (eILVar v))
      wrEqZero t = eEqZero (eReadMap (eWrPtr state t p) (eILVar v))
      wrGtZero t = eLe eZero (eReadMap (eWrPtr state t p) (eILVar v))

schedPredsOfConfig :: TyMap -> Config Int -> Symbol -> [Pred]
schedPredsOfConfig m Config {cProcs = ps} s
  = go <$> filter isAbs (fst <$> ps)
  where
    go p = schedPredOfPid m p s
           
predToString :: Pred -> String
predToString = show . pprint

lhSpec :: String -> String
lhSpec x = "{-@\n" ++ x ++ "\n@-}"

specBind :: String -> String -> String
specBind x s = x ++ " :: " ++ s

specFmt :: String
specFmt = "{-@ assume %s :: {v:%s | %s} @-}" 

printSpec :: String -> String -> Pred -> String
printSpec x t p = printf specFmt x t (predToString p)

initStateReft :: Pred -> String                  
initStateReft p
  = printSpec initialStateString stateTyString p

initSchedReft :: (Symbol -> [Pred]) -> String
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

mapGetSpec :: String
mapGetSpec
  = printf "{-@ %s :: m:Map_t k v -> k:k -> {v:v | v = Map_select m k} @-}" mapGetString

mapPutSpec :: String
mapPutSpec
  = printf "{-@ %s :: m:Map_t k v -> k:k -> v:v -> {vv:Map_t k v | vv = Map_store m k v } @-}" mapPutString

embedMap :: [String]
embedMap = [ "{-@ embed Map_t as Map_t @-}"
           , "{-@ measure Map_select :: Map_t k v -> k -> v @-}"
           , "{-@ measure Map_store :: Map_t k v -> k -> v -> Map_t k v @-}"
           , mapGetSpec, mapPutSpec
           ]

measuresOfConfig :: Config Int -> String
measuresOfConfig Config { cProcs = ps }
  = unlines [ printf "{-@ measure %s @-}" (unName $ pidInjectiveName p) | (p, _) <- ps]

builtinSpec :: [String]
builtinSpec = nonDetSpec : embedMap 

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

stateRecordSpec :: TyMap -> Config Int -> String
stateRecordSpec tm c
  = unlines [ printf "{-@ %s @-}" (prettyPrint st)
            , measuresOfConfig c
            , recQuals st
            ]
    where
      st = stateTypeOfConfig tm c

valTypeSpec :: String
valTypeSpec = printf "{-@ %s @-}" (prettyPrint valDecl)

initSpecOfConfig :: TyMap -> Config Int -> String               
initSpecOfConfig tm c
  = unlines [ initStateReft concPred
            , initSchedReft schedPreds
            , stateRecordSpec tm c
            , valTypeSpec
            ]
    
    where
      concPred   = pAnd  ((initOfPid tm <$> cProcs c) ++
                          [ eEqZero (eReadState (symbol "v") (vSym v)) | V v <- iters ])
      vSym       = symbol . prefix stateString
      iters      = everything (++) (mkQ [] goVars) (cProcs c)
      goVars :: Stmt Int -> [Var]
      goVars SIter {iterVar = v} = [v]
      goVars _                   = []
      schedPreds = schedPredsOfConfig tm c 

recvTy :: [Stmt Int] -> [ILType]
recvTy = everything (++) (mkQ [] go)
  where
    go :: Stmt Int -> [ILType]
    go (SRecv (t, _) _) = [t]
    go _                 = []
