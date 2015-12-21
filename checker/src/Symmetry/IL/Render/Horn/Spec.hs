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
import Symmetry.IL.Render.Horn.Types

instance Symbolic HsName where
  symbol (HsIdent x) = symbol x

eEqZero :: Expr -> Pred                       
eEqZero e = PAtom Eq e (expr (0 :: Int))                       

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
-- {-@ {v:Sched   

-- PC[PID] = 0
-- RD[PID,t] = 0
-- WR[PID,t] = 0
initOfConcPid :: TyMap -> Pid -> Pred
initOfConcPid m p@(PConc _)
  = pAnd (pcEqZero :
          concat [[rdEqZero t, wrEqZero t] | t <- snd <$> m ])
    where
      s          = "v"
      pcEqZero   = eEqZero (eReadMap (eReadState s pcName) (pidToExpr p))
      rdEqZero t = eEqZero (eReadMap (eReadState s ptrrName) (ePtrKey (pidToExpr p) (expr t)))
      wrEqZero t = eEqZero (eReadMap (eReadState s ptrwName) (ePtrKey (pidToExpr p) (expr t)))
           
-- get (state_PC initialState) PID_vP0 == 0 && get (state_PtrR initialState) (PtrKey PID_vP0 0) == 0 && get (state_PtrW initialState) (PtrKey PID_vP0 0) == 0
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

eRange :: Expr -> Expr -> Expr -> Pred
eRange v elow ehigh
  = pAnd [PAtom Le elow v, PAtom Lt v ehigh]
schedPredOfPid :: TyMap -> Pid -> Symbol -> Pred
schedPredOfPid m p@(PAbs (V v) (S s)) state
  = subst1 (pAnd ([pcEqZero, idxBounds] ++
                  concat [[rdEqZero t, wrEqZero t] | t <- snd <$> m]))
           (symbol (idxNameOfPid p), eVar "v")
    where
      idxBounds  = eRange (eVar "v") (expr (0 :: Int)) (eReadState state (prefix stateString s))
      pcEqZero   = eEqZero (eReadMap (eReadState state pcName) (pidToExpr p))
      rdEqZero t = eEqZero (eReadMap (eReadState state ptrrName) (ePtrKey (pidToExpr p) (expr t)))
      wrEqZero t = eEqZero (eReadMap (eReadState state ptrwName) (ePtrKey (pidToExpr p) (expr t)))

schedPredsOfConfig :: TyMap -> Config Int -> Symbol -> [Pred]
schedPredsOfConfig m Config {cProcs = ps} s
  = go <$> filter isAbs (fst <$> ps)
  where
    go p = schedPredOfPid m p s

mapGetSpec :: String
mapGetSpec
  = printf "{-@ assume %s :: m:Map k v -> k:k -> {v:v | v = Map_select m k} @-}" mapGetString

mapPutSpec :: String
mapPutSpec
  = printf "{-@ assume %s :: m:Map k v -> k:k -> v:v -> {vv:Map k v | vv = Map_store m k v } @-}" mapPutString

embedMap :: [String]
embedMap = [ "{-@ embed Map as Map_t @-}"
           , "{-@ measure Map_select :: Map k v -> k -> v @-}"
           , "{-@ measure Map_store :: Map k v -> k -> v -> Map k v @-}"
           , mapGetSpec, mapPutSpec
           ]

defaultMeasures :: [String]
defaultMeasures = [ printf "{-@ measure %s @-}" ptrrString
                  , printf "{-@ measure %s @-}" ptrwString
                  , printf "{-@ measure %s @-}" pcString
                  , printf "{-@ measure %s @-}" msgBufString
                  ] 

measuresOfConfig :: Config Int -> String
measuresOfConfig Config { cProcs = ps }
  = unlines ms
  where
    ms           = defaultMeasures ++ injectivePid ++ fields ++ sets
    vs           = nub $ listify (const True) (snd <$> ps)
    sets         = [ printf "{-@ measure %s @-}" (prefix stateString s) | (PAbs _ (S s), _) <- ps ]
    fields       = [ printf "{-@ measure %s @-}" (prefix stateString v) | (V v) <- vs ]
    injectivePid = [ printf "{-@ measure %s @-}" (unName $ pidInjectiveName p) | (p, _) <- ps]

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

initSpecOfConfig :: TyMap -> Config Int -> String               
initSpecOfConfig tm c
  = unlines [ initStateReft concPred
            , initSchedReft schedPreds
            , measuresOfConfig c
--            , pidSpecString c
            ]
    
    where
      concPred   = pAnd ([ initOfConcPid tm p | (p@(PConc _), _)  <- cProcs c ] ++
                         [  eEqZero (eReadState (symbol "v") (symbol $ prefix stateString v)) | V v <- iters ])
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
