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

eZero :: Expr
eZero = expr (0 :: Int)

eEqZero :: Expr -> Pred                       
eEqZero e = eEq e (expr (0 :: Int))                       

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

initOfConcPid :: TyMap -> Pid -> Pred
initOfConcPid m p@(PConc _)
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
schedPredOfPid m p@(PAbs (V v) (S s)) state
  = subst1 (pAnd ([pcEqZero, idxBounds] ++
                  concat [[rdEqZero t, wrEqZero t, wrGtZero t] | t <- snd <$> m]))
           (symbol (idxNameOfPid p), eVar "v")
    where
      idxBounds  = eRange (eVar "v") (expr (0 :: Int)) (eReadState state (prefix stateString s))
      pcEqZero   = eEqZero (eReadMap (eReadState state (pcName p)) (eVar v))
      rdEqZero t = eRangeI eZero (eReadMap (eRdPtr state t p) (eVar v)) (eReadMap (eWrPtr state t p) (eVar v))
      wrEqZero t = eEqZero (eReadMap (eWrPtr state t p) (eVar v))
      wrGtZero t = eLe eZero (eReadMap (eWrPtr state t p) (eVar v))

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

mapGetSpec :: String
mapGetSpec
  = printf "{-@ assume %s :: m:Map_t k v -> k:k -> {v:v | v = Map_select m k} @-}" mapGetString

mapPutSpec :: String
mapPutSpec
  = printf "{-@ assume %s :: m:Map_t k v -> k:k -> v:v -> {vv:Map_t k v | vv = Map_store m k v } @-}" mapPutString

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
builtinSpec = embedMap ++
              [ printf "{-@ data %s = %s { x%s_0 :: %s, x%s_1 :: Int } @-}"
                      ptrKeyTyString ptrKeyTyString
                      ptrKeyTyString pidTyString ptrKeyTyString
              , printf "{-@ data %s = %s { x%s_0 :: %s, x%s_1 :: Int, x%s_2 :: Int } @-}"
                      msgKeyTyString msgKeyTyString
                      msgKeyTyString pidTyString msgKeyTyString msgKeyTyString
              ]

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

valTypeSpec = printf "{-@ %s @-}" (prettyPrint valDecl)

initSpecOfConfig :: TyMap -> Config Int -> String               
initSpecOfConfig tm c
  = unlines [ initStateReft concPred
            , initSchedReft schedPreds
            , stateRecordSpec tm c
            , valTypeSpec
--            , pidSpecString c
            ]
    
    where
      concPred   = pAnd ([ initOfConcPid tm p | (p@(PConc _), _)  <- cProcs c ] ++
                         [  eEq (eReadState (symbol "v") (vSym v)) initExp | V v <- iters ])
      initExp    = expr (-1 :: Int)
      vSym       = symbol . prefix stateString
      iters      = everything (++) (mkQ [] goVars) (cProcs c)
      goVars :: Stmt Int -> [Var]
      goVars SIter {iterVar = v} = [v]
      goVars _                   = []
      schedPreds = schedPredsOfConfig tm c 

-----------------------
-- Qualifier Generation
-----------------------

-- recvQualsOfStmt :: TyMap
--                 -> (Pid, , NodeMap (Stmt Int))
--                 -> String
-- recvQualsOfStmt m (p, s, doms, nm)
--   = undefined

-- recvQualsOfProc :: TyMap
--                 -> (Pid, Gr (Stmt Int) (), NodeMap (Stmt Int))
--                 -> String
-- recvQualsOfProc m (p, cfg, nm)
--   = unlines [ recvQualsOfStmt m (p, s, myDom s, nm) | s <- listify go p ]
--   where
--     go = const True :: Stmt Int -> Bool
--     doms = dom cfg 0
--     myDom :: Stmt Int -> [Int]
--     myDom s = filter (/= annot s) . fromJust $ lookup (annot s) doms

-- qualsOfProc :: TyMap
--             -> (Pid, Gr (Stmt Int) ())
--             -> String
-- qualsOfProc m (p, cfg)
--   = recvQualsOfProc m (p, cfg, nm)
--   where
--     nm = fromGraph cfg

recvQualsOfStmt m s
  = undefined
  -- where
  --   recvs  = recvTys
  --   me     = annot s
  --   myDoms = fromJust $ lookup me doms
    

-- recvQualsOfProc m (p, cfg, nm)
--   =

qualsOfProc = undefined

recvTy :: [Stmt Int] -> [ILType]
recvTy = everything (++) (mkQ [] go)
  where
    go :: Stmt Int -> [ILType]
    go (SRecv (t, _) _) = [t]
    go _                 = []

qualsOfConfig :: Config Int -> TyMap -> String
qualsOfConfig Config { cProcs = ps } m
  = unlines [ qualsOfProc p | p <- ps ]
  where
    cfgs     = [ (p, toGraph (nextStmts s) (stmtMap s)) | (p, s) <- ps ]
    toGraph :: M.IntMap [Int] -> M.IntMap (Stmt Int) -> Gr (Stmt Int) ()
    toGraph g sm = let nodes = [ (i, sm M.! i) | i <- M.keys g ]
                       edges = [ (i,j,()) | (i, js) <- M.toList g, j <- js ]
                   in mkGraph nodes edges
    stmtMap  = M.fromList . everything (++) (mkQ [] go)
    go :: Stmt Int -> [(Int, Stmt Int)]
    go s = [(annot s, s)]
