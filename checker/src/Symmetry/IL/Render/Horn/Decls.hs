{-# Language TemplateHaskell #-}
{-# Language ScopedTypeVariables #-}
module Symmetry.IL.Render.Horn.Decls where

import           Data.Map
import           Data.List       as List
import           Data.Generics hiding (empty)
import           Control.Monad.Reader
import           Language.Haskell.Syntax
import           Language.Haskell.Pretty

import           Symmetry.IL.AST as AST
import           Symmetry.IL.Render.Horn.Config
import           Symmetry.IL.Render.Horn.Types

basicDataDecl n tvs cs clss 
  = HsDataDecl emptyLoc [] n tvs cs clss
recordDataDecl r n fs
  = basicDataDecl n [] [HsRecDecl emptyLoc r fs]

pcTypeNameOfPid :: Pid -> String
pcTypeNameOfPid p = prefix "PC" $ pidString p
    
pcTypeOfProc :: Process Int
             -> HsDecl
pcTypeOfProc (p, s)
  = basicDataDecl tyName [] [tagCon (locName p i) | i <- locs] [eqClass]
  where
    tyName = name $ pcTypeNameOfPid p
    locs = everything (++) (mkQ [] go) s
    go :: AST.Stmt Int -> [Int]
    go s = [annot s]

stateFieldsOfProc :: Process Int -> [([HsName], HsBangType)]
stateFieldsOfProc (p, s)
  = if isAbs p then [ roleField p, unfolded p ]++ (goAbs <$> fs) else go <$> fs
  where
    fs = [name (prefix stateString v) | V v <- vs ]
    vs = recvVars s ++ patVars s
    go f = ([f], bangTy valType)
    goAbs f = ([f], bangTy $ intMapType valType)
    roleField  (PAbs _ (S s)) = ([name (prefix stateString s)], bangTy intType)
    unfolded q@(PAbs _ (S s)) = ([pidUnfoldName q], bangTy intType)

intFieldsOfProc :: Process Int -> [([HsName], HsBangType)]              
intFieldsOfProc (p, s)
  = if isAbs p then doAbs <$> vars else do1 <$> vars
  where
    do' (V v) t = ([name $ prefix stateString v], bangTy t)
    doAbs v     = do' v (intMapType intType)
    do1   v     = do' v intType
    vars        = everything (++) (mkQ [] go) s
    go :: Stmt Int -> [Var]
    go (SIter { iterVar = i }) = [i]
    go (SLoop { loopVar = (LV i) }) = [V i]
    go (SChoose { chooseVar = v }) = [v]
    go _                       = []

countersOfProc :: Process Int
                  -> [([HsName], HsBangType)]
countersOfProc (p@(PAbs _ _), s)
  = [ ([pcCounterName], bangTy pcCounterTy)
    , ([rdCounterName], bangTy rdCounterTy)
    , ([wrCounterName], bangTy wrCounterTy)
    ]
  where
    pcCounterName = pidLocCounterName p
    pcCounterTy   = mapType intType intType
    rdCounterName = pidRdCounterName p
    rdCounterTy   = mapType intType intType
    wrCounterName = pidWrCounterName p
    wrCounterTy   = mapType intType intType
countersOfProc _
  = []

pidInjectiveFns :: ConfigInfo a -> [HsDecl]
pidInjectiveFns CInfo { config = Config { cProcs = ps }}
  = [ HsFunBind $ fnMatch p | (p, _) <- ps ]
    where
      fnName    = name . prefix "is" . unName . pidNameOfPid
      trueRHS   = HsUnGuardedRhs true
      falseRHS  = HsUnGuardedRhs false
      fnMatch p = [ HsMatch emptyLoc (fnName p) [pidPatOfPid p] trueRHS []
                  , HsMatch emptyLoc (fnName p) [HsPWildCard] falseRHS  []
                  ]
      
pidTypeOfConfig :: ConfigInfo a -> [HsDecl]
pidTypeOfConfig c@CInfo{ config = Config { cProcs = ps }}
  = [ basicDataDecl prePidTyName ts fs [eqClass]
    , HsTypeDecl emptyLoc pidTyName [] pidTyApp] ++
    pidInjectiveFns c
  where
    pidTyApp = List.foldl' HsTyApp (ty prePidTyName) (const intType <$> ts)
    (absPs, concPs) = List.partition isAbs (fst <$> ps)
    ts = (\(PAbs _ (S s)) -> name s) <$> absPs
    fs = [tagCon (pidNameOfPid p)                  | p <- concPs] ++
         [valCon (pidNameOfPid p) [bangTy (ty t)] | (p,t) <- zip absPs ts ]

ptrsOfProc :: ConfigInfo Int -> Process Int -> [([HsName], HsBangType)]
ptrsOfProc ci (p, _)
  = concatMap go ts
    where
      go :: Integer -> [([HsName], HsBangType)]
      go t = [ ([pidRdPtrName t p], bangTy ptrTy)
             , ([pidWrPtrName t p], bangTy ptrTy)
             , ([pidMsgBufName t p], bangTy bufTy)
             ]
      ptrTy = if isAbs p then mapType intType intType else intType
      bufTy = if isAbs p then vec2DType valType else vecType valType
      ts = snd <$> (tyMap ci)

pcOfProc :: Process Int -> ([HsName], HsBangType)
pcOfProc (p, _)
  = ([pcName p], bangTy pcType)
  where
    pcType = if isAbs p then mapType intType intType else intType

stateFieldsOfConfig :: ConfigInfo Int -> [([HsName], HsBangType)]
stateFieldsOfConfig ci 
  = concatMap stateFieldsOfProc ps ++
    concatMap intFieldsOfProc   ps ++ 
    concatMap countersOfProc    ps ++
    concatMap (ptrsOfProc ci)   ps ++
    fmap      pcOfProc          ps ++
    [ ([name (prefix stateString v)], bangTy valType) | (V v, _) <- gs ]
  where
    ps = cProcs   (config ci)
    gs = cGlobals (config ci)

stateTypeOfConfig :: ConfigInfo Int
                  -> HsDecl
stateTypeOfConfig ci
  = recordDataDecl stateTyName stateTyName (stateFieldsOfConfig ci) []

pcTypesOfConfig :: Config Int -> [HsDecl]
pcTypesOfConfig Config { cProcs = ps }
  = pcTypeOfProc <$> ps

nonDetDecls :: [ HsDecl ]
nonDetDecls = [ nonDetTypeDecl, nonDetDecl ]
  where
    nonDetTypeDecl = HsTypeSig emptyLoc [nonDetName] (HsQualType [] (schedTy $->$ intType))
    nonDetDecl     = HsFunBind [HsMatch emptyLoc nonDetName [] (HsUnGuardedRhs (var "undefined")) []]

-- mapDecls :: [HsDecl]
-- mapDecls = [ mapTypeDecl, mapGetType, mapGetDecl, mapPutType, mapPutDecl{- , ptrKeyTyDecl, msgKeyTyDecl -} ]
--   where
--     k = name "k"
--     v = name "v"
--     kt = HsTyVar k
--     vt = HsTyVar v
--     mapt = HsTyApp (HsTyApp (HsTyCon (UnQual mapTyName)) kt) vt
--     mapTypeDecl = HsDataDecl emptyLoc [] mapTyName [k, v] [] []
--     mapGetDecl  = HsFunBind [HsMatch emptyLoc mapGetName [] (HsUnGuardedRhs (var "undefined")) []]
--     mapPutDecl  = HsFunBind [HsMatch emptyLoc mapPutName [] (HsUnGuardedRhs (var "undefined")) []]
--     mapGetType  = HsTypeSig emptyLoc [mapGetName] (HsQualType [] (mapt $->$ kt $->$ vt))
--     mapPutType  = HsTypeSig emptyLoc [mapPutName] (HsQualType [] (mapt $->$ kt $->$ vt $->$ mapt))
--     ptrKeyTyDecl= HsDataDecl emptyLoc [] ptrKeyTyName [] [HsConDecl emptyLoc ptrKeyTyName [ bangTy pidType
--                                                                                           , bangTy intType
--                                                                                           ]] [eqClass]
--     msgKeyTyDecl= HsDataDecl emptyLoc [] msgKeyTyName [] [HsConDecl emptyLoc msgKeyTyName [ bangTy pidType
--                                                                                           , bangTy intType
--                                                                                           , bangTy intType
--                                                                                           ]] [eqClass]

valDecl :: HsDecl
valDecl
  = HsDataDecl emptyLoc [] valTyName [] (uncurry recCon <$> valConstructors) []
  where
    recCon n ts  = HsRecDecl emptyLoc n [ ([accessor n i], t) | (t, i) <- zip ts [0..]]
    accessor n i = name ("v" ++ unName n ++ show i)

valFunctions :: [HsDecl]
valFunctions
  = HsTypeSig emptyLoc (valInjective . fst <$> valConstructors) (HsQualType [] (valType $->$ boolType))
  : (mkMeasure . fst <$> valConstructors)
  where
    trueRhs     = HsUnGuardedRhs true
    falseRhs    = HsUnGuardedRhs false
    mkMeasure n = HsFunBind [ HsMatch emptyLoc (valInjective n) [HsPRec (UnQual n) []] trueRhs []
                            , HsMatch emptyLoc (valInjective n) [HsPWildCard] falseRhs []
                            ]

declsOfConfig :: ConfigInfo Int -> [HsDecl]    
declsOfConfig ci
  = [valDecl, stateTypeOfConfig ci] ++
    valFunctions ++
    pidTypeOfConfig ci ++
    nonDetDecls
