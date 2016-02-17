{-# Language ParallelListComp #-}
{-# Language ViewPatterns #-}
{-# Language ScopedTypeVariables #-}
module Symmetry.IL.Model.HaskellSpec where

-- import           Data.Char
import           Data.Generics
-- import qualified Data.IntMap.Strict as M
-- import qualified Data.IntSet as S
-- import qualified Data.Map.Strict as Map
import           Data.Foldable as Fold
import           Data.List
import           Data.Maybe
import           Language.Haskell.Exts.Pretty
import           Language.Haskell.Exts.Syntax hiding (Stmt)
import           Language.Haskell.Exts.SrcLoc
import           Language.Haskell.Exts.Build
import           Language.Fixpoint.Types as F
import           Text.Printf

import qualified Symmetry.IL.AST as IL hiding (Op(..))
import           Symmetry.IL.AST (ident, isAbs, Stmt(..), Pid(..), Set(..), Var(..), Config(..))
import           Symmetry.IL.ConfigInfo
import           Symmetry.IL.Model
import           Symmetry.IL.Model.HaskellDefs

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

eLt :: F.Expr -> F.Expr -> F.Expr            
eLt e1 e2 = PAtom Lt e1 e2            

eGt :: F.Expr -> F.Expr -> F.Expr            
eGt e1 e2 = PAtom Gt e1 e2            

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
eApp f = eApps (F.eVar f)

eImp p q
  = F.PImp p q

pidToExpr :: IL.Pid -> F.Expr        
pidToExpr p@(PConc _) = eVar $ pid p        
pidToExpr p@(PAbs (V v) (S s)) = eApp (pid p) [eVar $ pidIdx p]

eReadState :: (Symbolic a, Symbolic b) => a -> b -> F.Expr                        
eReadState s f 
  = eApp (symbol f) [eVar s]

eReadMap e k
  = eApp "Map_select" {- mapGetSpecString -} [e, k]

eRdPtr, eWrPtr :: (IL.Identable i, Symbolic a)
               => ConfigInfo i -> IL.Pid -> IL.Type -> a -> F.Expr
eRdPtr ci p t s
  = eReadState s (ptrR ci p t)
eWrPtr ci p t s
  = eReadState s (ptrW ci p t)

initOfPid :: forall a. (Data a, IL.Identable a)
          => ConfigInfo a -> IL.Process a -> F.Expr
initOfPid ci (p@(PAbs _ (S s)), stmt)
  = pAnd preds 
  where
    preds    = [ counterInit
               , unfoldInit
               , eRange (eReadState st eK)
                 eZero (eReadState st (pidBound p))
               , eEq counterSum setSize
               ] ++
               counterInits
                 
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
    go :: Stmt a -> [Int]
    go s = [ident s]

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
      firstNonBlock Block { blkBody = bs } = ident (head bs)
      firstNonBlock s                      = ident s

schedExprOfPid :: IL.Identable a
               => ConfigInfo a -> IL.Pid -> Symbol -> F.Expr
schedExprOfPid ci p@(IL.PAbs v (IL.S s)) state
  = subst1 (pAnd ([pcEqZero, idxBounds] ++
                  concat [[rdEqZero t, wrEqZero t, wrGtZero t] | t <- fst <$> tyMap ci]))
           (symbol (pidIdx p), eVar "v")
    where
      idxBounds  = eRange (eVar "v") (F.expr (0 :: Int)) (eReadState state s)
      pcEqZero   = eEqZero (eReadMap (eReadState state (pc p)) (eILVar v))
      rdEqZero t = eRangeI eZero (eReadMap (eRdPtr ci p t state) (eILVar v)) (eReadMap (eWrPtr ci p t state) (eILVar v))
      wrEqZero t = eEqZero (eReadMap (eWrPtr ci p t state) (eILVar v))
      wrGtZero t = eLe eZero (eReadMap (eWrPtr ci p t state) (eILVar v))

schedExprsOfConfig :: IL.Identable a
                   => ConfigInfo a -> Symbol -> [F.Expr]
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

measuresOfConfig :: Config a -> String
measuresOfConfig Config { cProcs = ps }
  = unlines [ printf "{-@ measure %s @-}" (pidInj p) | (p, _) <- ps]

valMeasures :: String
valMeasures
  = unlines [ printf "{-@ measure %s @-}" (valInj v) | v <- valCons ]

builtinSpec :: [String]
builtinSpec = [nonDetSpec]

---------------------
-- Type Declarations
---------------------
intType, mapTyCon :: Type
intType  = TyCon (UnQual (name "Int"))
mapTyCon = TyCon (UnQual (name "Map_t"))

mapType :: Type -> Type -> Type
mapType k v = TyApp (TyApp mapTyCon k) v

stateRecord :: [([Name], Type)] -> QualConDecl
stateRecord fs
  = QualConDecl noLoc [] [] (RecDecl (name stateRecordCons) fs)
  
removeDerives                           :: Decl -> Decl
removeDerives (DataDecl s d c n ts qs _) = DataDecl s d c n ts qs []
removeDerives _                          = undefined

---------------
-- State Fields
---------------

withStateFields ci f absF pcF ptrF valF intF globF globIntF
  = f ([ absF p (pidBound p) (pidUnfold p) (pcCounter p) | p <- pids ci, isAbs p ] ++
       [ pcF p  (pc p)        | p <- pids ci ] ++
       [ ptrF p (ptrR ci p t) (ptrW ci p t) | p <- pids ci, t <- fst <$> tyMap ci ] ++
       [ valF p v | (p, v) <- valVars (stateVars ci) ]  ++
       [ intF p v | (p, v) <- intVars (stateVars ci) ]  ++
       [ globF v | v <- globVals (stateVars ci) ] ++
       [ globIntF v | V v <- setBoundVars ci ])

stateDecl :: ConfigInfo a
          -> ([Decl], String)
stateDecl ci
  = ([dataDecl], specStrings)
  where
    derivin      = [(UnQual $ name "Show", []) | isQC ci] 
    dataDecl     = DataDecl noLoc DataType [] (name stateRecordCons) [] [stateRecord fs] derivin
    specStrings  = unlines [ dataReft
                           , ""
                           , recQuals
                           , ""
                           ]

    -- remove deriving classes (lh fails with them)
    dataReft     = printf "{-@ %s @-}" (pp (removeDerives dataDecl))
    fs = withStateFields ci concat absF mkPC mkPtrs mkVal mkInt mkGlob mkGlobInt 
    absF _ b unf pcv = [mkBound b, mkCounter pcv, mkUnfold unf]
    mkPtrs p rd wr  = mkInt p rd ++ mkInt p wr
    mkGlob v        = [([name v], valHType ci)]
    mkGlobInt v     = [([name v], intType)]

    mkUnfold p  = ([name p], intType)
    mkBound p   = ([name p], intType)
    mkCounter p = ([name p], mapType intType intType)
    recQuals = unlines [ mkDeref f t ++ "\n" ++ mkEq f | ([f], t) <- fs ]

    mkDeref f t = printf "{-@ qualif Deref_%s(v:%s, w:%s): v = %s w @-}"
                          (pp f) (pp t) stateRecordCons (pp f) 
    mkEq f = printf "{-@ qualif Eq_%s(v:%s, w:%s ): %s v = %s w @-}"
                     (pp f) stateRecordCons stateRecordCons (pp f) (pp f)
    mkPC  = liftMap intType
    mkVal = liftMap (valHType ci)
    mkInt = liftMap intType
    liftMap t p v = [([name v], if isAbs p then mapType intType t else t)]

valHType :: ConfigInfo a -> Type
valHType ci = TyApp (TyCon (UnQual (name valType)))
                    (pidPreApp ci)

pidPreApp ci
  = foldl' TyApp (TyCon . UnQual $ name pidPre) pidPreArgs
  where
    pidPreArgs :: [Type]
    pidPreArgs = const intType <$> filter isAbs (pids ci)

pidDecl :: ConfigInfo a
        -> [Decl]
pidDecl ci
  = [ DataDecl noLoc DataType [] (name pidPre) tvbinds cons [(UnQual $ name "Show",[])]
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

pidFn :: IL.Pid -> Decl
pidFn p
  = FunBind [ Match noLoc (name $ pidInj p) [pidPattern p] Nothing truerhs Nothing
            , Match noLoc (name $ pidInj p) [PWildCard] Nothing falserhs Nothing
            ]
  where
    truerhs = UnGuardedRhs (var (sym "True"))
    falserhs = UnGuardedRhs (var (sym "False"))

boundPred :: IL.SetBound -> F.Expr
boundPred (IL.Known (S s) n)
  = eEq (F.expr n) (eReadState "v" s)
boundPred (IL.Unknown (S s) (V x))
  = eEq (eReadState "v" x) (eReadState "v" s)

initSpecOfConfig :: (Data a, IL.Identable a)
                 => ConfigInfo a -> String
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
     ++ (unlines $ scrapeQuals ci)
    
    where
      concExpr   = pAnd  ((initOfPid ci <$> cProcs (config ci)) ++
                          [ eEqZero (eReadState (symbol "v") (symbol v))
                            | V v <- iters ] ++
                          [ eGt (eReadState (symbol "v") (symbol v)) eZero
                            | S v <- globSets (stateVars ci) ] ++ -- TODO do not assume this...
                          catMaybes [ boundPred <$> setBound ci s | (PAbs _ s) <- pids ci ])
      iters      = everything (++) (mkQ [] goVars) (cProcs (config ci))
      goVars :: IL.Stmt Int -> [Var]
      goVars Iter {iterVar = v} = [v]
      goVars _                   = []
      schedExprs = schedExprsOfConfig ci
      (stateDecls, stateSpec) = stateDecl ci
      pidDecls = pidDecl ci

recvTy :: [IL.Stmt Int] -> [IL.Type]
recvTy = everything (++) (mkQ [] go)
  where
    go :: IL.Stmt Int -> [IL.Type]
    go (Recv (t, _) _) = [t]
    go _                 = []

---------------------
-- Qualifiers                           
---------------------
mkQual :: String
       -> [(String, String)]
       -> F.Expr
       -> String
mkQual n args e
  = printf "{-@ qualif %s(%s): %s @-}" n argString eString 
  where
    eString = show $ pprint e
    argString = intercalate ", " (go <$> args)
    go (a,t) = printf "%s:%s" a t

scrapeQuals :: (IL.Identable a, Data a)
            => ConfigInfo a
            -> [String]
scrapeQuals ci
  = scrapeIterQuals ci ++
    scrapeAssertQuals ci

scrapeIterQuals :: (Data a, IL.Identable a)
                => ConfigInfo a
                -> [String]
scrapeIterQuals ci
  = concat [ everything (++) (mkQ [] (go p)) s | (p, s) <- cProcs (config ci) ]
  where
    go :: IL.Pid -> IL.Stmt Int -> [String]
    go p Iter { iterVar = V v, iterSet = S set, iterBody = b, annot = a }
      = [mkQual "IterInv" [("v", stateRecordCons)]
          (eImp (eReadState "v" (pc p) `eEq` F.expr i)
                (eReadState "v" v `eEq` eReadState "v" set)) | i <- pcAfter (ident a)] ++
        iterQuals p v set b
    go _ _
      = []
    pcAfter i = (-1) : [ j | j <- pcVals, j > i ]
    pcVals :: [Int]
    pcVals = Fold.foldl (\is (_, s) -> ident s : is) [] (cProcs $ config ci)
        

iterQuals :: (IL.Identable a, Data a)
          => IL.Pid -> String -> String -> IL.Stmt a -> [String]
iterQuals p@(PConc _) v set b
  = [mkQual "IterInv" [("v", stateRecordCons)]
            (eReadState "v" v `eLe` eReadState "v" set)] ++
    everything (++) (mkQ [] go) b
  where
    go :: IL.Stmt Int -> [String]
    go s
       = [mkQual "Iter" [("v", stateRecordCons)]
                         (pcImpl p (ident s) (eReadState "v" v `eLt` eReadState "v" set))]

pcImpl :: IL.Pid -> Int -> F.Expr -> F.Expr
pcImpl p i e
  = eImp (eReadState "v" (pc p) `eEq` (F.expr i)) e

scrapeAssertQuals :: ConfigInfo a
                  -> [String]
scrapeAssertQuals _
  = []
