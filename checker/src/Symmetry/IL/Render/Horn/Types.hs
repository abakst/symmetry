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
mapTyString = "Map_t"
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
pidString (PConc i)      = prefix "vP" $ show i
pidString (PAbs _ (S s)) = prefix "vP" s

pidWrPtrString :: Integer -> Pid -> String                               
pidWrPtrString = pidPtrString ptrwString

pidRdPtrString :: Integer -> Pid -> String                               
pidRdPtrString = pidPtrString ptrrString

pidMsgBufString :: Integer -> Pid -> String
pidMsgBufString t p = prefix stateString .
                      prefix (pidString p) .
                      prefix msgBufString $ show t

pidMsgBufName :: Integer -> Pid -> HsName
pidMsgBufName t p = name $ pidMsgBufString t p

pidPtrString :: String -> Integer -> Pid -> String
pidPtrString s t p
  = prefix stateString .
    prefix s .
    prefix (pidString p) $ show t

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

pidRdPtrName t p = name $ pidRdPtrString t p                 
pidWrPtrName t p = name $ pidWrPtrString t p                 

locName p i = name ("L_" ++ pidString p ++ "_" ++ show i)

prefix x y = x ++ "_" ++ y              

stateString   = "state"             
stateTyString = "State"
pcString p    = prefix stateString . prefix (pidString p) $ "PC"
ptrrString    = "PtrR"
ptrwString    = "PtrW"
msgBufString  = "Buf"
stateTyName = name stateTyString
stateName   = name stateString
pcName p    = name (pcString p)
ptrrName    = name ptrrString
ptrwName    = name ptrwString
msgBufName  = name msgBufString

pidNameOfPid p = name (pidTyString `prefix` pidString p)              

pidInjectiveName :: Pid -> HsName
pidInjectiveName = name . prefix "is" . unName . pidNameOfPid

idxNameOfPid (PAbs (V v) _)  = name v
idxNameOfPid (PAbs (GV v) _) = name v

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

bufKeyTy :: Pid -> HsType
bufKeyTy p =
  if isAbs p then
    HsTyTuple [intType, intType]
  else
    intType
          

----------------------                 
-- Util Expressions
----------------------                 
true, false :: HsExp
true = HsCon (UnQual (name "True"))
false = HsCon (UnQual (name "False"))

pidVar :: Var -> HsExp
pidVar (V v)  = var v        
pidVar (GV v) = var v        

var :: String -> HsExp
var = HsVar . UnQual . name

varn :: HsName -> HsExp
varn = HsVar . UnQual

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

-- field :: HsName -> HsName -> HsExp
-- field f s = HsParen (HsApp (HsVar (UnQual f) ) (HsVar (UnQual s)))

readGlobal :: String -> HsExp
readGlobal f = (var $ prefix stateString f) 

readStateField :: Pid -> String -> HsExp            
readStateField p f = if isAbs p then
                       readMap (varn fname)
                               (varn (idxNameOfPid p))
                     else
                       varn fname
  where
    fname = name $ prefix stateString f

stateField :: String -> HsExp
stateField f = var (prefix stateString f)

updField :: Pid -> String -> HsExp -> HsFieldUpdate
updField p f e
  = if isAbs p then
      HsFieldUpdate (UnQual fname) (writeMap (stateField f) (HsVar (UnQual (idxNameOfPid p))) e)
    else
      HsFieldUpdate (UnQual fname) e
  where
    fname = name $ prefix stateString f

readPCMap :: Pid -> HsExp
readPCMap p@(PConc _)      = pcState p
readPCMap p@(PAbs v _) = readMap (pcState p) (pidVar v)

updPC :: Pid -> Int -> Int -> [HsFieldUpdate]
updPC p pc pc'
  = if isAbs p then
      [ HsFieldUpdate (UnQual (pcName p)) (writeMap (pcState p) (varn (idxNameOfPid p)) pce')
      , pcku
      ]
    else
      [ HsFieldUpdate (UnQual (pcName p)) pce' ]
  where
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
    pcu = HsFieldUpdate (UnQual (pcName p))
          (writeMap (pcState p) (pidCstrOfPid p) pce')
    pce' = HsParen $ HsIf grd (int pc') (int pc'')

expToVal :: Pid -> ILExpr -> HsExp
expToVal p EUnit        = unitCons
expToVal p EInt         = intCons
expToVal p (EVar (V v)) = readStateField p v
expToVal p (EPid q)     = pidCons $>$ pidCstrOfPid q

pcState :: Pid -> HsExp
pcState p = varn $ pcName p

pidPCCounterState :: Pid -> HsExp
pidPCCounterState p = varn (pidLocCounterName p)

ptrrState :: Integer -> Pid -> HsExp          
ptrrState t p = varn (pidRdPtrName t p) 

msgBufState :: Integer -> Pid -> HsExp                
msgBufState t p
  = varn (pidMsgBufName t p) 

ptrwState :: Integer -> Pid -> HsExp          
ptrwState t p = varn (pidWrPtrName t p)

pidWrCounterState :: Pid -> HsExp
pidWrCounterState p = varn (pidWrCounterName p)

pidRdCounterState :: Pid -> HsExp
pidRdCounterState p = varn (pidRdCounterName p)

readMap :: HsExp -> HsExp -> HsExp
readMap m k = HsParen (HsApp (HsApp mapGet m) k)

writeMap :: HsExp -> HsExp -> HsExp -> HsExp
writeMap m k v = HsParen (mapPut $>$ m $>$ k $>$ v)

mkPtrKey :: Pid -> Pid -> Integer -> HsExp
mkPtrKey me p@(PConc _) t
  = int t
mkPtrKey me p@(PAbs (GV v) _) t
  = var v
mkPtrKey me p@(PAbs (V v) _) t
  = readStateField me v

mkMsgKey :: Pid -> Pid -> HsExp -> HsExp
mkMsgKey me p@(PConc _) e      = e
mkMsgKey me p@(PAbs (V v) _) e = HsParen (tuple_con 1 $>$ readStateField me v $>$ e)
mkMsgKey me p@(PAbs (GV v) _) e = HsParen (tuple_con 1 $>$ var v $>$ e)
-- mkMsgKey k1 k2 k3 = HsParen (HsCon (UnQual msgKeyTyName) $>$ k1 $>$ k2 $>$ k3)

readPtrr :: Integer -> Pid -> HsExp
readPtrr i p@(PConc _)  = ptrrState i p
readPtrr i p@(PAbs v _) = readMap (ptrrState i p) (pidVar v)

readPtrw :: Pid -> Integer -> Pid -> HsExp
readPtrw me i p@(PConc _)       = ptrwState i p
readPtrw me i p@(PAbs (V v) _)  = readMap (ptrwState i p) (readStateField me v)
readPtrw me i p@(PAbs (GV v) _) = readMap (ptrwState i p) (var v)

readMyPtrr p tid = readPtrr tid p
readMyPtrw p@(PConc _) tid       = ptrwState tid p
readMyPtrw p@(PAbs (GV v) _) tid = readMap (ptrwState tid p) (var v)
readMyPtrw p@(PAbs (V v) _) tid  = error "readMyPtrW -- Shouldn't happen?" -- readMap (ptrwState tid p) (var v)

readMsgBuf :: Pid -> Integer -> HsExp
readMsgBuf me@(PConc _) t
  = readMap (msgBufState t me) (readPtrr t me)
readMsgBuf me@(PAbs (GV v) _) t
  = readMap (msgBufState t me) (HsParen (tuple_con 1 $>$ var v $>$ readPtrr t me))
readMsgBuf me@(PAbs (V v) _) t
  = error "readMsgBuf Shouldn't happen?" -- readMap (msgBufState t me) (HsParen (tuple_con 1 $>$ var v $>$ readPtrr t me))

writeMsgBuf :: Pid -> Pid -> Integer -> ILExpr -> HsFieldUpdate         
writeMsgBuf p q t e
  = HsFieldUpdate (UnQual (pidMsgBufName t q))
      (writeMap (msgBufState t q) (mkMsgKey p q (readPtrw p t q)) (HsParen (expToVal p e)))

-- A pid might be indexed by a local variable, so we need 'p'
-- in order to look that variable up
pidExprOfPid :: Pid -> Pid -> HsExp           
pidExprOfPid _ q@(PConc _)
  = pidCstrOfPid q
pidExprOfPid p q@(PAbs (V v) (S s))
  = HsParen (HsCon (UnQual (pidNameOfPid q)) $>$ readStateField p v)

ptrwUpdate :: Integral a => a -> Pid -> Pid -> HsExp
ptrwUpdate t p q@(PConc _)
  = inc (readPtrw p (toInteger t) q)
ptrwUpdate t p q@(PAbs _ _)
  = writeMap (ptrwState (toInteger t) q)
      (mkPtrKey p q (toInteger t))
      (inc (readPtrw p (toInteger t) q))

incPtrw :: Integral a => a -> Pid -> Pid -> [HsFieldUpdate]
incPtrw t p q
  = if isAbs q then
      [ptrUpd, ptrCtrUpd]
    else
      [ptrUpd]
    where
      ptrUpd    = HsFieldUpdate (UnQual (pidWrPtrName (toInteger t) q)) (ptrwUpdate t p q)
      ptrCtrUpd = HsFieldUpdate (UnQual (pidWrCounterName q)) incPtrCtr
      incPtrCtr = writeMap (pidWrCounterState q)
                           tid 
                           (inc (readMap (pidWrCounterState q) tid))
      tid = int $ toInteger t

incPtrr :: Integral a => a -> Pid -> [HsFieldUpdate]
incPtrr t p
  = if isAbs p then
      [ HsFieldUpdate (UnQual (pidRdPtrName (toInteger t) p))
         (writeMap (ptrrState (toInteger t) p)
                   (varn (idxNameOfPid p))
                   (inc (readPtrr (toInteger t) p)))
      , ptrCtrUpd
      ]
    else
      [ HsFieldUpdate (UnQual (pidRdPtrName (toInteger t) p))
          (inc (readPtrr (toInteger t) p))
      ]
    where
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

pcEq :: Pid -> Integer -> HsExp                
pcEq p i = readPCMap p `eq` HsParen (HsLit (HsInt i))

assert :: HsExp -> HsExp
assert e
  = var "liquidAssert" $>$ e $>$ HsCon (Special HsUnitCon)
