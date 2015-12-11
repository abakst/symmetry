module Symmetry.IL.Render.Horn.Types where

import           Data.Map
import           Data.Maybe
import           Data.List as List
import           Data.Generics           hiding (empty)
import           Control.Monad.Reader
import           Language.Haskell.Syntax
import           Language.Haskell.Pretty
import           Symmetry.IL.AST         as AST

type TyMap = [(ILType, Integer)]                 

lookupTy :: ILType -> TyMap -> Integer
lookupTy t = fromJust . List.lookup t

safeFromList :: (Ord k)
            => [(k,v)]
            -> Map k v
safeFromList l
  = fromListWith err l
  where
    err = error "safeFromList: joining non-disjoint maps"

emptyLoc = SrcLoc "" (-1) (-1)

tagCon :: HsName -> HsConDecl
tagCon i = HsConDecl emptyLoc i []

valCon :: HsName -> [HsBangType] -> HsConDecl
valCon i ts = HsConDecl emptyLoc i ts

schedString = "sched"              
schedName   = name schedString

pidTyString = "PID"
intTyString = "Int"
valTyString = "Val"
mapTyString = "Map"

pidTyName = name pidTyString
intTyName = name intTyString
valTyName = name valTyString
mapTyName = name mapTyString

unitValConsName = name "Unit"
intValConsName  = name "Int"
pidValConsName  = name "Pid"            
leftValConsName  = name "InL"
rightValConsName  = name "InR"
prodValConsName  = name "Pair"

unitCons = HsCon (UnQual unitValConsName)                   
intCons = HsCon (UnQual intValConsName)                   
pidCons = HsCon (UnQual pidValConsName)                   

ty n      = HsTyCon (UnQual n)
bangTy t  = HsUnBangedTy t
valType   = ty valTyName
intType   = ty intTyName
pidType   = ty pidTyName
mapType k v = HsTyApp (HsTyApp (ty mapTyName) k) v
intMapType t = mapType intType t

vCon :: HsName -> HsConDecl
vCon i = HsConDecl emptyLoc i [bangTy valType]

name :: String -> HsName
name = HsIdent              

pidString :: Pid -> String
pidString (PConc i)          = "vP" ++ show i
pidString (PAbs (V v) (S s)) = prefix "vP" (prefix s v)

locName p i = name ("L_" ++ pidString p ++ "_" ++ show i)

prefix x y = x ++ "_" ++ y              

stateString = "state"             
stateTyName = name "State"
stateName   = name stateString
pcName      = name $ prefix stateString "PC"
ptrrName    = name $ prefix stateString "PtrR"
ptrwName    = name $ prefix stateString "PtrW"
msgBufName  = name $ prefix stateString "Buf"

pidNameOfPid p = name (pidTyString `prefix` pidString p)              
idxNameOfPid (PAbs (V v) (S s)) = name (prefix "idx" (prefix s v))

pidCstrOfPid p@(PConc _)    = HsCon (UnQual (pidNameOfPid p))
pidCstrOfPid p@(PAbs _ _)   = HsParen (HsApp (HsCon (UnQual (pidNameOfPid p)))
                                             (HsVar (UnQual (idxNameOfPid p))))

-- pidPatOfPid (V v)        = HsPVar (name v)                                  
pidPatOfPid p@(PConc _)  = HsPApp (UnQual (pidNameOfPid p)) []                            
pidPatOfPid p@(PAbs _ _) = HsPApp (UnQual (pidNameOfPid p)) [HsPVar (idxNameOfPid p)]

mapGetName = name $ "get"
mapPutName = name $ "put"

runStateName = name $ "runState"
checkName    = name $ "check"
initialName  = name $ "initial"
             

----------------------                 
-- Util Expressions
----------------------                 
var = HsVar . UnQual . name

int :: Integral a => a -> HsExp      
int = HsLit . HsInt . toInteger

inc :: HsExp -> HsExp
inc e = HsParen (HsParen (HsVar (UnQual (name "+"))) $>$ e $>$ int 1)

op :: String -> HsExp
op = HsParen . HsVar . UnQual . name

eq :: HsExp -> HsExp -> HsExp
eq e1 e2 = HsApp (HsApp (op "==") e1) e2

lneg :: HsExp -> HsExp
lneg e = var "not" $>$ HsParen e

lt :: HsExp -> HsExp -> HsExp
lt e1 e2 = HsParen (HsApp (HsApp (op "<") e1) e2)

lte :: HsExp -> HsExp -> HsExp
lte e1 e2 = HsParen (HsApp (HsApp (op "<=") e1) e2)

ands :: [HsExp] -> HsExp
ands []     = HsCon (UnQual (name "True"))
ands [x]    = HsParen x
ands (x:xs) = HsApp (HsApp (op "&&") (HsParen x)) $ ands xs

ors :: [HsExp] -> HsExp
ors []     = HsCon (UnQual (name "False"))
ors [x]    = HsParen x
ors (x:xs) = HsApp (HsApp (op "||") (HsParen x)) $ ors xs

ifLte i n e1 e2              
  = HsIf (lte i n) e1 e2

infixl 9 $>$
m $>$ n = HsApp m n

listHead :: HsPat -> HsPat -> HsPat          
listHead pat rest
  = HsPApp (Special (HsCons)) [HsPParen pat, rest]

----------------------                 
-- Access State Fields
----------------------                 
mapGet :: HsExp
mapGet = HsVar (UnQual mapGetName)

mapPut :: HsExp
mapPut = HsVar (UnQual mapPutName)

field :: HsName -> HsName -> HsExp
field f s = HsParen (HsApp (HsVar (UnQual f) ) (HsVar (UnQual s)))

readStateField :: Pid -> String -> HsExp            
readStateField p f = if isAbs p then
                   readMap (field fname stateName)
                           (HsVar (UnQual (idxNameOfPid p)))
                 else
                   field fname stateName
  where
    fname = name $ prefix stateString f

stateField :: String -> HsExp
stateField f = field fname stateName
  where
    fname = name $ prefix stateString f

updField :: Pid -> String -> HsExp -> HsFieldUpdate
updField p f e
  = if isAbs p then
      HsFieldUpdate (UnQual fname) (writeMap (stateField f) (HsVar (UnQual (idxNameOfPid p))) e)
    else
      HsFieldUpdate (UnQual fname) e
  where
    fname = name $ prefix stateString f

updPC :: Pid -> HsExp -> HsFieldUpdate            
updPC p pc'
  = HsFieldUpdate (UnQual pcName) (writeMap pcState (pidCstrOfPid p) pc')

expToVal :: Pid -> ILExpr -> HsExp
expToVal p EUnit        = unitCons
expToVal p EInt         = intCons
expToVal p (EVar (V v)) = readStateField p v
expToVal p (EPid q)     = pidCons $>$ pidCstrOfPid q

pcState :: HsExp
pcState = field pcName stateName

ptrrState :: HsExp          
ptrrState = field ptrrName stateName

ptrwState :: HsExp          
ptrwState = field ptrwName stateName

msgBufState :: HsExp
msgBufState = field msgBufName stateName            

readMap :: HsExp -> HsExp -> HsExp
readMap m k = HsParen (HsApp (HsApp mapGet m) k)

writeMap :: HsExp -> HsExp -> HsExp -> HsExp
writeMap m k v = HsParen (mapPut $>$ m $>$ k $>$ v)

readPtrr :: Integer -> HsExp -> HsExp
readPtrr i p = readMap ptrrState (HsTuple [p, HsLit (HsInt i)])

readPtrw :: Integer -> HsExp -> HsExp
readPtrw i p = readMap ptrwState (HsTuple [p, HsLit (HsInt i)])

readMsgBuf :: Pid -> Integer -> HsExp
readMsgBuf p t = readMap msgBufState (HsTuple [pe, int t, readPtrr t pe])
  where
    pe = pidCstrOfPid p

writeMsgBuf :: Pid -> Pid -> Integer -> ILExpr -> HsFieldUpdate         
writeMsgBuf p q t e
  = HsFieldUpdate (UnQual msgBufName)
      (writeMap msgBufState (HsTuple [pe, int t, readPtrw t pe]) (HsParen (expToVal p e)))
    where
      pe = pidCstrOfPid q

readPCMap :: HsExp -> HsExp
readPCMap p = readMap pcState p

ptrwUpdate t p
  = writeMap ptrwState
      (HsTuple [pidCstrOfPid p, int (toInteger t)])
      (inc (readPtrw (toInteger t) (pidCstrOfPid p)))

incPtrw :: Integral a => a -> Pid -> HsFieldUpdate
incPtrw t p = HsFieldUpdate (UnQual ptrwName) (ptrwUpdate t p)
                            

incPtrwVar :: Integral a => [Pid] -> Pid -> a -> Var -> HsFieldUpdate
incPtrwVar dom from t (V to)
  = HsFieldUpdate (UnQual ptrwName)
      (HsCase (readStateField from to)
              ([HsAlt emptyLoc (pat p) (alt p) [] | p <- dom] ++
               [HsAlt emptyLoc HsPWildCard (HsUnGuardedAlt assumeFalse) []]))
  where
    assumeFalse = var "liquidAssume" $>$ (HsCon (UnQual (name "False")))
                                     $>$ var "undefined"
    pat p = HsPApp (UnQual pidValConsName) [pidPatOfPid p]
    alt = HsUnGuardedAlt . ptrwUpdate t
     -- HsFieldUpdate (UnQual ptrwName)
     --              (writeMap ptrrState
     --                        (HsCase
     --                        (HsTuple [readStateField from to, int (toInteger t)])
     --                        (inc (readPtrw (toInteger t) (readStateField from to))))

incPtrr :: Integral a => a -> Pid -> HsFieldUpdate
incPtrr t p = HsFieldUpdate (UnQual ptrrName)
                            (writeMap ptrrState
                                      (HsTuple [pidCstrOfPid p, int (toInteger t)])
                                      (inc (readPtrr (toInteger t) (pidCstrOfPid p))))

updateState us
  = HsRecUpdate (HsVar (UnQual stateName)) us 

pcEq :: HsExp -> Integer -> HsExp                
pcEq p i = readPCMap p `eq` HsParen (HsLit (HsInt i))

pidReadTy p tid  = readPtrr tid (pidCstrOfPid p)
pidWriteTy p tid = readPtrw tid (pidCstrOfPid p)

assert :: HsExp -> HsExp
assert e
  = var "liquidAssert" $>$ e $>$ HsCon (Special HsUnitCon)
