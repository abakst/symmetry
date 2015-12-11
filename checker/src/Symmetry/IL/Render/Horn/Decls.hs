{-# Language TemplateHaskell #-}
{-# Language ScopedTypeVariables #-}
module Symmetry.IL.Render.Horn.Decls where

import           Data.Map
import           Data.Generics hiding (empty)
import           Control.Monad.Reader
import           Language.Haskell.Syntax
import           Language.Haskell.Pretty

import           Symmetry.IL.AST as AST
import           Symmetry.IL.Render.Horn.Types

basicDataDecl n cs
  = HsDataDecl emptyLoc [] n [] cs []             
recordDataDecl r n fs
  = basicDataDecl n [HsRecDecl emptyLoc r fs]

pcTypeNameOfPid :: Pid -> String
pcTypeNameOfPid p = prefix "PC" $ pidString p
    
pcTypeOfProc :: Process Int
             -> HsDecl
pcTypeOfProc (p, s)
  = basicDataDecl tyName [tagCon (locName p i) | i <- locs]
  where
    tyName = name $ pcTypeNameOfPid p
    locs = everything (++) (mkQ [] go) s
    go :: AST.Stmt Int -> [Int]
    go s = [annot s]

recvVars :: forall a. (Data a, Typeable a) => AST.Stmt a -> [Var]
recvVars s
  = everything (++) (mkQ [] go) s
  where
    go :: AST.Stmt a -> [Var]
    go (SRecv t _) = listify (const True) t
    go _           = []

stateFieldsOfProc :: Process Int -> [([HsName], HsBangType)]
stateFieldsOfProc (p, s)
  = if isAbs p then goAbs <$> fs else go <$> fs
  where
    fs = [name (prefix stateString v) | V v <- vs ]
    vs = recvVars s
    go f = ([f], bangTy valType)
    goAbs f = ([f], bangTy $ intMapType valType)

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
    go _                       = []

pidTypeOfConfig :: Config a -> HsDecl
pidTypeOfConfig Config { cProcs = ps }
  = basicDataDecl pidTyName fs
  where
    fs = [tagCon (pidNameOfPid p)                  | (p@(PConc _),_)  <- ps] ++
         [valCon (pidNameOfPid p) [bangTy intType] | (p@(PAbs _ _),_) <- ps]

rdPtrMap, wrPtrMap, pcMap, bufMap :: ([HsName], HsBangType)
rdPtrMap
  = ([ptrrName], bangTy (mapType keyTy valTy))
     where
       keyTy = HsTyTuple [pidType, intType]
       valTy = intType
wrPtrMap
  = ([ptrwName], bangTy (mapType keyTy valTy))
     where
       keyTy = HsTyTuple [pidType, intType]
       valTy = intType
pcMap
  = ([pcName], bangTy (mapType keyTy valTy))
     where
       keyTy = pidType
       valTy = intType
bufMap
  = ([msgBufName], bangTy (mapType keyTy valTy))
    where
      keyTy = HsTyTuple [pidType, intType, intType]
      valTy = valType
           
stateTypeOfConfig :: Config Int
                  -> HsDecl
stateTypeOfConfig Config { cProcs = ps }
  = recordDataDecl stateTyName stateTyName procState
  where
    procState = concatMap stateFieldsOfProc ps ++
                concatMap intFieldsOfProc ps   ++
                [ rdPtrMap, wrPtrMap, bufMap, pcMap ]

pcTypesOfConfig :: Config Int -> [HsDecl]
pcTypesOfConfig Config { cProcs = ps }
  = pcTypeOfProc <$> ps

mapDecls :: [HsDecl]
mapDecls = [ mapTypeDecl, mapGetType, mapGetDecl, mapPutType, mapPutDecl ]
  where
    k = name "k"
    v = name "v"
    kt = HsTyVar k
    vt = HsTyVar v
    mapt = HsTyApp (HsTyApp (HsTyCon (UnQual mapTyName)) kt) vt
    mapTypeDecl = HsDataDecl emptyLoc [] mapTyName [k, v] [] []
    mapGetDecl  = HsFunBind [HsMatch emptyLoc mapGetName [] (HsUnGuardedRhs (var "undefined")) []]
    mapPutDecl  = HsFunBind [HsMatch emptyLoc mapPutName [] (HsUnGuardedRhs (var "undefined")) []]
    mapGetType  = HsTypeSig emptyLoc [mapGetName] (HsQualType [] (mapt $->$ kt $->$ vt))
    mapPutType  = HsTypeSig emptyLoc [mapPutName] (HsQualType [] (mapt $->$ kt $->$ vt $->$ mapt))

infixr 5 $->$
t1 $->$ t2 = HsTyFun t1 t2                                                                                                     

valDecl :: HsDecl
valDecl = HsDataDecl emptyLoc [] valTyName [] [ con unitValConsName []
                                              , con intValConsName [bangTy intType]
                                              , con pidValConsName [bangTy pidType]
                                              , con leftValConsName [bangTy valType]
                                              , con rightValConsName [bangTy valType]
                                              , con prodValConsName [bangTy valType, bangTy valType]
                                              ] []
  where
    con = HsConDecl emptyLoc

declsOfConfig :: Config Int -> [HsDecl]    
declsOfConfig c
  = [pidTypeOfConfig c, stateTypeOfConfig c] ++ valDecl : mapDecls
