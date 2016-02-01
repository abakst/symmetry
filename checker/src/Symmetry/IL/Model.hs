{-# Language MultiParamTypeClasses #-}
{-# Language FunctionalDependencies #-}
module Symmetry.IL.Model where

import Prelude hiding (and)
import Data.Generics
import Data.Char
import Symmetry.IL.AST
import Symmetry.IL.Render.Horn.Config

-- Values    
unitCons, nullCons, intCons, stringCons, pidCons, leftCons, rightCons, pairCons :: String
unitCons   = "VUnit"
nullCons   = "VUnInit"
intCons    = "VInt"
stringCons = "VString"
pidCons    = "VPid"
rightCons  = "VInR"
leftCons   = "VInL"
pairCons   = "VPair"

-- Generating Names                    
prefix :: String -> String -> String
prefix x (y:ys) = x ++ (toUpper y : ys)

pid :: Pid -> String
pid (PConc i)      = prefix "pid" . prefix "r" $ show i
pid (PAbs _ (S s)) = prefix "pid" s
pid _ = error "pid: non conc or abs"

pidIdx :: Pid -> String
pidIdx (PAbs (V v) _)  = v
pidIdx (PAbs (GV v) _) = v
pidIdx _               = error "pidIdx of non-abs"

pc :: Pid -> String
pc p = prefix (pid p) "pc"

stateRecordCons = "State"
pidPre          = "Pid_pre"
pidType         = "Pid"

pidTyName ci p t s
  = prefix (pid p) . prefix s $ show tid
  where
    tid = lookupTy ci t

buf :: ConfigInfo Int -> Pid -> ILType -> String
buf ci p t = pidTyName ci p t "buf"

ptrR :: ConfigInfo Int -> Pid -> ILType -> String           
ptrR ci p t = pidTyName ci p t "ptrR"

ptrW :: ConfigInfo Int -> Pid -> ILType -> String           
ptrW ci p t = pidTyName ci p t "ptrW"


mapGetFn, mapPutFn, vecGetFn, vecPutFn :: String
mapGetFn = "get"
mapPutFn = "put"
vecGetFn = "getVec"
vec2DGetFn = "getVec2D"
vecPutFn = "setVec"
vec2DPutFn = "setVec2D"

state :: String
state = "state"

data Rule e = Rule Pid [(String, e)] e e --[(String, e)], [((Pid, ILType), e)])

class ILModel e where
  -- names
  -- pc        :: ConfigInfo Int -> Pid -> e
  -- ptrR      :: ConfigInfo Int -> Pid -> ILType -> e
  -- ptrW      :: ConfigInfo Int -> Pid -> ILType -> e
  -- expressions
  expr      :: ILExpr -> e
  incr      :: e -> e
  eq        :: e -> e -> e
  and       :: e -> e -> e
  lt        :: e -> e -> e
  lte       :: e -> e -> e
  int       :: Int -> e
  readPC    :: ConfigInfo Int -> Pid -> e
  readPtrR  :: ConfigInfo Int -> Pid -> ILType -> e
  readPtrW  :: ConfigInfo Int -> Pid -> Pid -> ILType -> e
  readState :: ConfigInfo Int -> Pid -> String -> e

  -- updates
  joinUpdate :: ConfigInfo Int -> Pid -> e -> e -> e
  setPC      :: ConfigInfo Int -> Pid -> e -> e
  incrPtrR   :: ConfigInfo Int -> Pid -> ILType -> e
  incrPtrW   :: ConfigInfo Int -> Pid -> Pid -> ILType -> e
  setState   :: ConfigInfo Int -> Pid -> [(String , e)] -> e
  putMessage :: ConfigInfo Int -> Pid -> Pid -> (ILExpr, ILType) -> e
  getMessage :: ConfigInfo Int -> Pid -> (Var, ILType) -> e

  -- rule
  matchVal :: ConfigInfo Int -> Pid -> String -> ILExpr -> Rule e -> Rule e
  rule     :: ConfigInfo Int -> Pid -> e -> e -> Rule e

  printModel :: ConfigInfo Int -> [Rule e] -> String

pcGuard :: ILModel e => ConfigInfo Int -> Pid -> Stmt Int -> e
pcGuard ci p s = readPC ci p `eq` int (annot s)

nextPC :: ILModel e => ConfigInfo Int -> Pid -> Stmt Int -> e
nextPC ci p s = nextPC' ci p $ cfgNext ci p (annot s)
  where
    nextPC' ci p Nothing
      = setPC ci p (int (-1))
    nextPC' ci p (Just [s])
      = setPC ci p (int (annot s))

-------------------------
-- Statement "semantics"    
-------------------------
seqUpdates ci p = foldl1 (joinUpdate ci p)

ruleOfStmt :: ILModel e => ConfigInfo Int -> Pid -> Stmt Int -> [Rule e]
ruleOfStmt ci p s@SSend { sndPid = EPid q, sndMsg = (t, e) }
  = [rule ci p grd (seqUpdates ci p upds)]
  where
    grd  = pcGuard ci p s
    upds = [ incrPtrW ci p q t
           , putMessage ci p q (e, t)
           , nextPC ci p s
           ]
    
ruleOfStmt ci p s@SSend { sndPid = EVar (V x) }
  = concat [ matchVal ci p x (EPid q) <$> ruleOfStmt ci p (sub q) | q <- pids ci ]
    where
      sub q = s { sndPid = EPid q }
    
              
ruleOfStmt ci p s@SRecv{ rcvMsg = (t, v) }
  = [ rule ci p grd (seqUpdates ci p upds) ]
  where
    grd  = pcGuard ci p s `and`
           (readPtrR ci p t `lt` readPtrW ci p p t)
    upds = [ incrPtrR ci p t
           , getMessage ci p (v,t)
           , nextPC ci p s
           ]

ruleOfStmt ci p s
  = [ rule ci p (pcGuard ci p s) (nextPC ci p s) ]

ruleOfProc :: (ILModel e) => ConfigInfo Int -> Process Int -> [Rule e]
ruleOfProc c (p, s)
  = concatMap (ruleOfStmt c p) ss
  where
    ss = listify (const True) s

rulesOfConfigInfo :: ILModel e => ConfigInfo Int -> [Rule e]
rulesOfConfigInfo c
  = concatMap (ruleOfProc c) ps
  where
    ps = cProcs (config c)

generateModel :: ILModel e => Config () -> (ConfigInfo Int, [Rule e])
generateModel c
  = (cinfo, rulesOfConfigInfo cinfo)
  where
    cinfo = mkCInfo c { cProcs = (freshStmtIds <$>) <$> cProcs c }
