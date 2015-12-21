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

prePidTyString = "PID_pre"
pidTyString = "PID"
intTyString = "Int"
valTyString = "Val"
ptrKeyTyString = "PtrKey"
msgKeyTyString = "MsgKey"
mapTyString = "Map"
pcCounterMapString = "PCK"
rdCounterString = "RdK"
wrCounterString = "WrK"

prePidTyName = name prePidTyString
pidTyName = name pidTyString
intTyName = name intTyString
valTyName = name valTyString
ptrKeyTyName = name ptrKeyTyString
msgKeyTyName = name msgKeyTyString
mapTyName = name mapTyString

unitValConsName = name "VUnit"
intValConsName  = name "VInt"
pidValConsName  = name "VPid"            
leftValConsName  = name "VInL"
rightValConsName  = name "VInR"
prodValConsName  = name "VPair"

unitCons = HsCon (UnQual unitValConsName)                   
intCons = HsCon (UnQual intValConsName)                   
pidCons = HsCon (UnQual pidValConsName)                   

ty n      = HsTyCon (UnQual n)
bangTy t  = HsUnBangedTy t
valType   = ty valTyName
intType   = ty intTyName
pidType   = ty pidTyName
prePidType   = ty prePidTyName
mapType k v = HsTyApp (HsTyApp (ty mapTyName) k) v
intMapType t = mapType intType t

vCon :: HsName -> HsConDecl
vCon i = HsConDecl emptyLoc i [bangTy valType]

name :: String -> HsName
name = HsIdent              

unName :: HsName -> String
unName (HsIdent n) = n       

eqClass = UnQual (name "Eq")

pidString :: Pid -> String
pidString (PConc i)          = prefix "vP" $ show i
pidString (PAbs (V v) (S s)) = prefix "vP" s

pidLocCounterString :: Pid -> String
pidLocCounterString p
  = prefix stateString $
    prefix (pidString p) pcCounterMapString

pidRdCounterString :: Pid -> String
pidRdCounterString p
  = prefix stateString $
    prefix (pidString p) rdCounterString

pidWrCounterString :: Pid -> String
pidWrCounterString p
  = prefix stateString $
    prefix (pidString p) wrCounterString

pidLocCounterName :: Pid -> HsName
pidLocCounterName p
  = name $ pidLocCounterString p

pidRdCounterName :: Pid -> HsName
pidRdCounterName p
  = name $ pidRdCounterString p

pidWrCounterName :: Pid -> HsName
pidWrCounterName p
  = name $ pidWrCounterString p

locName p i = name ("L_" ++ pidString p ++ "_" ++ show i)

prefix x y = x ++ "_" ++ y              

stateString = "state"             
stateTyString = "State"
pcString    = prefix stateString "PC"
ptrrString    = prefix stateString "PtrR"
ptrwString    = prefix stateString "PtrW"
msgBufString  = prefix stateString "Buf"
stateTyName = name stateTyString
stateName   = name stateString
pcName      = name pcString
ptrrName    = name ptrrString
ptrwName    = name ptrwString
msgBufName  = name msgBufString

pidNameOfPid p = name (pidTyString `prefix` pidString p)              

pidInjectiveName :: Pid -> HsName
pidInjectiveName = name . prefix "is" . unName . pidNameOfPid

idxNameOfPid (PAbs (V v) _) = name v

pidCstrOfPid p@(PConc _)    = HsCon (UnQual (pidNameOfPid p))
pidCstrOfPid p@(PAbs _ _)   = HsParen (HsApp (HsCon (UnQual (pidNameOfPid p)))
                                             (HsVar (UnQual (idxNameOfPid p))))
idxTyNames :: [Pid] -> [HsName]
idxTyNames ps
  = zipWith const (name <$> ["i" ++ show i | _ <- ps, i <- [0..]]) ps
-- pidPatOfPid (V v)        = HsPVar (name v)                                  
pidPatOfPid p@(PConc _)  = HsPApp (UnQual (pidNameOfPid p)) []                            
pidPatOfPid p@(PAbs _ _) = HsPApp (UnQual (pidNameOfPid p)) [HsPVar (idxNameOfPid p)]

mapGetString = "get"                           
mapGetSpecString = "Map_select"
mapPutString = "put"                           
mapPutSpecString = "Map_store"
mapGetName = name mapGetString
mapPutName = name mapPutString

runStateName = name $ "runState"
checkName    = name $ "check"

initialStateString = "initialState"
initialName        = name initialStateString

initialSchedString = "initialSched"
initialSchedName   = name initialSchedString

schedTy = HsTyApp list_tycon pidType

----------------------                 
-- Util Expressions
----------------------                 
true, false :: HsExp
true = HsCon (UnQual (name "True"))
false = HsCon (UnQual (name "False"))

var = HsVar . UnQual . name

int :: Integral a => a -> HsExp      
int n = if n < 0 then HsParen e else e
  where e = HsLit (HsInt (toInteger n))

inc :: HsExp -> HsExp
inc e = HsParen (HsParen (HsVar (UnQual (name "+"))) $>$ e $>$ int 1)

dec :: HsExp -> HsExp
dec e = HsParen (HsParen (HsVar (UnQual (name "-"))) $>$ e $>$ int 1)

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
ands (x:xs) = HsParen (HsApp (HsApp (op "&&") (HsParen x)) $ ands xs)

ors :: [HsExp] -> HsExp
ors []     = HsCon (UnQual (name "False"))
ors [x]    = HsParen x
ors (x:xs) = HsParen (HsApp (HsApp (op "||") (HsParen x)) $ ors xs)

impl :: HsExp -> HsExp -> HsExp
impl e1 e2 = ors [lneg e1, e2]

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

readGlobal :: String -> HsExp
readGlobal f = field (name $ prefix stateString f) stateName

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

updPC :: Pid -> Int -> Int -> [HsFieldUpdate]
updPC p pc pc'
  = if isAbs p then
      [pcu, pcku]
    else
      [pcu]
  where
    pcu = HsFieldUpdate (UnQual pcName)
          (writeMap pcState (pidCstrOfPid p) pce')
    pcku = HsFieldUpdate (UnQual (pidLocCounterName p))
                         (writeMap (writeMap pcmap pce
                                               (dec (readMap pcmap pce)))
                                   pce'
                                   (inc (readMap pcmap pce')))
    pcmap = pidPCCounterState p                                   
    pce  = int pc
    pce' = int pc'

condUpdPC :: Pid -> HsExp -> Int -> Int -> Int -> [HsFieldUpdate]
condUpdPC p grd pc pc' pc''
  = if isAbs p then
      [pcu, pcku]
    else
      [pcu]
  where
    pcku = HsFieldUpdate (UnQual (pidLocCounterName p))
                         (writeMap (writeMap pcmap pce
                                               (dec (readMap pcmap pce)))
                                   pce'
                                   (inc (readMap pcmap pce')))
    pcmap = pidPCCounterState p                                   
    pce  = int pc
    pcu = HsFieldUpdate (UnQual pcName)
          (writeMap pcState (pidCstrOfPid p) pce')
    pce' = HsParen $ HsIf grd (int pc') (int pc'')

expToVal :: Pid -> ILExpr -> HsExp
expToVal p EUnit        = unitCons
expToVal p EInt         = intCons
expToVal p (EVar (V v)) = readStateField p v
expToVal p (EPid q)     = pidCons $>$ pidCstrOfPid q

pcState :: HsExp
pcState = field pcName stateName

pidPCCounterState :: Pid -> HsExp
pidPCCounterState p = field (pidLocCounterName p) stateName

ptrrState :: HsExp          
ptrrState = field ptrrName stateName

ptrwState :: HsExp          
ptrwState = field ptrwName stateName

pidWrCounterState :: Pid -> HsExp
pidWrCounterState p = field (pidWrCounterName p) stateName

pidRdCounterState :: Pid -> HsExp
pidRdCounterState p = field (pidRdCounterName p) stateName

msgBufState :: HsExp
msgBufState = field msgBufName stateName            

readMap :: HsExp -> HsExp -> HsExp
readMap m k = HsParen (HsApp (HsApp mapGet m) k)

writeMap :: HsExp -> HsExp -> HsExp -> HsExp
writeMap m k v = HsParen (mapPut $>$ m $>$ k $>$ v)

mkPtrKey :: HsExp -> HsExp -> HsExp
mkPtrKey k1 k2 = HsParen (HsCon (UnQual ptrKeyTyName) $>$ k1 $>$ k2)

mkMsgKey :: HsExp -> HsExp -> HsExp -> HsExp
mkMsgKey k1 k2 k3 = HsParen (HsCon (UnQual msgKeyTyName) $>$ k1 $>$ k2 $>$ k3)

readPtrr :: Integer -> HsExp -> HsExp
readPtrr i p = readMap ptrrState (mkPtrKey p (int i))

readPtrw :: Integer -> HsExp -> HsExp
readPtrw i p = readMap ptrwState (mkPtrKey p (int i))

readMsgBuf :: Pid -> Integer -> HsExp
readMsgBuf p t = readMap msgBufState (mkMsgKey pe (int t) (readPtrr t pe))
  where
    pe = pidCstrOfPid p

writeMsgBuf :: Pid -> Pid -> Integer -> ILExpr -> HsFieldUpdate         
writeMsgBuf p q t e
  = HsFieldUpdate (UnQual msgBufName)
      (writeMap msgBufState (mkMsgKey pe (int t) (readPtrw t pe)) (HsParen (expToVal p e)))
    where
      pe = pidExprOfPid p q 

-- A pid might be indexed by a local variable, so we need 'p'
-- in order to look that variable up
pidExprOfPid :: Pid -> Pid -> HsExp           
pidExprOfPid _ q@(PConc _)
  = pidCstrOfPid q
pidExprOfPid p q@(PAbs (V v) (S s))
  = HsParen (HsCon (UnQual (pidNameOfPid q)) $>$ readStateField p v)

readPCMap :: HsExp -> HsExp
readPCMap p = readMap pcState p

ptrwUpdate :: Integral a => a -> Pid -> Pid -> HsExp
ptrwUpdate t p q
  = writeMap ptrwState
      (mkPtrKey pe (int (toInteger t)))
      (inc (readPtrw (toInteger t) pe))
    where
      pe = pidExprOfPid p q 

incPtrw :: Integral a => a -> Pid -> Pid -> [HsFieldUpdate]
incPtrw t p q
  = if isAbs q then
      [ptrUpd, ptrCtrUpd]
    else
      [ptrUpd]
    where
      ptrUpd    = HsFieldUpdate (UnQual ptrwName) (ptrwUpdate t p q)
      ptrCtrUpd = HsFieldUpdate (UnQual (pidWrCounterName q)) incPtrCtr
      incPtrCtr = writeMap (pidWrCounterState q)
                           tid 
                           (inc (readMap (pidWrCounterState q) tid))
      tid = int $ toInteger t

incPtrr :: Integral a => a -> Pid -> [HsFieldUpdate]
incPtrr t p
  = if isAbs p then
      [ptrUpd, ptrCtrUpd]
    else
      [ptrUpd]
    where
      ptrUpd = HsFieldUpdate (UnQual ptrrName)
                             (writeMap ptrrState
                                (mkPtrKey (pidCstrOfPid p) tid)
                             (inc (readPtrr (toInteger t) (pidCstrOfPid p))))
      ptrCtrUpd = HsFieldUpdate (UnQual (pidRdCounterName p)) incPtrCtr
      incPtrCtr = writeMap (pidRdCounterState p)
                           tid 
                           (inc (readMap (pidRdCounterState p) tid))
      tid = int $ toInteger t

-- incPtrwVar :: Integral a => [Pid] -> Pid -> a -> Var -> HsFieldUpdate
-- incPtrwVar dom from t (V to)
--   = HsFieldUpdate (UnQual ptrwName)
--       (HsCase (readStateField from to)
--               ([HsAlt emptyLoc (pat p) (alt p) [] | p <- dom] ++
--                [HsAlt emptyLoc HsPWildCard (HsUnGuardedAlt assumeFalse) []]))
--   where
--     assumeFalse = var "liquidAssume" $>$ (HsCon (UnQual (name "False")))
--                                      $>$ var "undefined"
--     pat p = HsPApp (UnQual pidValConsName) [pidPatOfPid p]
--     alt = HsUnGuardedAlt . ptrwUpdate t from

updateState us
  = HsRecUpdate (HsVar (UnQual stateName)) us 

pcEq :: HsExp -> Integer -> HsExp                
pcEq p i = readPCMap p `eq` HsParen (HsLit (HsInt i))

pidReadTy p tid  = readPtrr tid (pidCstrOfPid p)
pidWriteTy p tid = readPtrw tid (pidCstrOfPid p)

assert :: HsExp -> HsExp
assert e
  = var "liquidAssert" $>$ e $>$ HsCon (Special HsUnitCon)
