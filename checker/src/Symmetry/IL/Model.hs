{-# Language MultiParamTypeClasses #-}
{-# Language FunctionalDependencies #-}
module Symmetry.IL.Model where

import Prelude hiding (and, or, pred)
import Text.Printf
import Data.Generics
import Data.Char
import Symmetry.IL.AST
import Symmetry.IL.ConfigInfo

import Text.PrettyPrint.Leijen (pretty)
import Debug.Trace

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

valCons :: [String]
valCons = [ unitCons
          , nullCons
          , intCons
          , stringCons
          , pidCons
          , rightCons
          , leftCons
          , pairCons
          ]

-- Constant Names
sched, state, initState, initSched, nondet, nondetRange :: String
state = "state"
sched = "sched"
initState = "state0"
initSched = "sched0"
nondet    = "nonDet"
nondetRange = "nonDetRange"

mapGetFn, mapPutFn, vecGetFn, vecPutFn :: String
mapGetFn = "get"
mapPutFn = "put"
vecGetFn = "getVec"
vec2DGetFn = "getVec2D"
vecPutFn = "setVec"
vec2DPutFn = "setVec2D"

-- Generating Names                    
prefix :: String -> String -> String
prefix x (y:ys) = x ++ (toUpper y : ys)

pid :: Pid -> String
pid (PConc i)      = prefix "pid" . prefix "r" $ show i
pid (PAbs _ (S s)) = prefix "pid" s
pid _ = error "pid: non conc or abs"

pidUnfold :: Pid -> String
pidUnfold p@(PAbs _ _) = prefix (pid p) "k"

pidIdx :: Pid -> String
pidIdx (PAbs (V v) _)  = v
pidIdx (PAbs (GV v) _) = v
pidIdx _               = error "pidIdx of non-abs"

pc :: Pid -> String
pc p = prefix (pid p) "pc"

pidPcCounter :: Pid -> String
pidPcCounter p = prefix (pid p) "pcK"

pidPre          = "Pid_pre"

pidTyName ci p t s
  = prefix (pid p) . prefix s $ show tid
  where
    tid = lookupTy ci t

buf :: ConfigInfo a -> Pid -> Type -> String
buf ci p t = pidTyName ci p t "buf"

ptrR :: ConfigInfo a -> Pid -> Type -> String           
ptrR ci p t = pidTyName ci p t "ptrR"

ptrW :: ConfigInfo a -> Pid -> Type -> String           
ptrW ci p t = pidTyName ci p t "ptrW"

data Rule e = Rule Pid e (Maybe e) e
              deriving Show

class ILModel e where
  true      :: e
  false     :: e
  expr      :: ConfigInfo a -> Pid -> ILExpr -> e
  pred      :: ConfigInfo a -> Pid -> Pred -> e
  add       :: e -> e -> e
  incr      :: e -> e
  decr      :: e -> e
  eq        :: e -> e -> e
  and       :: e -> e -> e
  or        :: e -> e -> e
  lneg      :: e -> e
  lt        :: e -> e -> e
  lte       :: e -> e -> e
  int       :: Int -> e

  readPC    :: ConfigInfo a -> Pid -> e
  readPCCounter :: ConfigInfo a -> Pid -> e -> e
  readPtrR  :: ConfigInfo a -> Pid -> Type -> e
  readPtrW  :: ConfigInfo a -> Pid -> Pid -> Type -> e
  readRoleBound :: ConfigInfo a -> Pid -> e
  readState :: ConfigInfo a -> Pid -> String -> e

  nonDet      :: ConfigInfo a -> Pid -> e
  nonDetRange :: ConfigInfo a -> Pid -> Set -> e
  matchVal    :: ConfigInfo a -> Pid -> e -> [(ILExpr, e)] -> e

  -- updates
  joinUpdate :: ConfigInfo a -> Pid -> e -> e -> e
  setPC      :: ConfigInfo a -> Pid -> e -> e
  incrPtrR   :: ConfigInfo a -> Pid -> Type -> e
  incrPtrW   :: ConfigInfo a -> Pid -> Pid -> Type -> e
  setState   :: ConfigInfo a -> Pid -> [(String , e)] -> e
  putMessage :: ConfigInfo a -> Pid -> Pid -> (ILExpr, Type) -> e
  getMessage :: ConfigInfo a -> Pid -> (Var, Type) -> e

  -- rule
  rule     :: ConfigInfo a -> Pid -> e -> Maybe e -> e -> Rule e

  printModel :: (Identable a, Data a) => ConfigInfo a -> [Rule e] -> String
  printCheck :: (Identable a, Data a) => ConfigInfo a -> [Rule e] -> String

-------------------------
-- "Macros"
-------------------------
ands :: ILModel e => [e] -> e
ands []     = true
ands [x]    = x
ands (x:xs) = foldr and x xs

ors :: ILModel e => [e] -> e
ors []     = false
ors [x]    = x
ors (x:xs) = foldr or x xs

pcGuard :: (Identable a, ILModel e)
        => ConfigInfo a -> Pid -> Stmt a -> e
pcGuard ci p s = readPC ci p `eq` int (ident s)

nextPC :: (Identable a, ILModel e)
       => ConfigInfo a -> Pid -> Stmt a -> e
nextPC ci p s = nextPC' ci p $ cfgNext ci p (ident s)
  where
    nextPC' ci' p' Nothing
      = setPC ci' p' (int (-1))
    nextPC' ci' p' (Just [s])
      = setPC ci' p' (int (ident s))
    nextPC' _ _ (Just _)
      = error "nextPC unexpected"

mkRule :: (Identable a, ILModel e)
       => ConfigInfo (PredAnnot a) -> Pid -> e -> e -> PredAnnot a -> Rule e
mkRule ci p grd bdy a
  = rule ci p grd exp bdy
  where
    exp = case (annotPred a) of
               ILPTrue -> Nothing
               q       -> Just (pred ci p q)
               
-------------------------
-- Statement "semantics"    
-------------------------
seqUpdates :: (Identable a, ILModel e)
           => ConfigInfo a -> Pid -> [e] -> e
seqUpdates ci p = foldl1 (joinUpdate ci p)

ruleOfStmt :: (Identable a, Data a, ILModel e)
           => ConfigInfo (PredAnnot a) -> Pid -> Stmt (PredAnnot a) -> [Rule e]
-------------------------
-- p!e::t
-------------------------
ruleOfStmt ci p s@Send { sndPid = EPid q, sndMsg = (t, e) }
  = [mkRule ci p grd (seqUpdates ci p upds) (annot s)]
  where
    grd  = pcGuard ci p s
    upds = [ incrPtrW ci p q t
           , putMessage ci p q (e, t)
           , nextPC ci p s
           ]
    
ruleOfStmt ci p s@Send { sndPid = x@EVar {} , sndMsg = (t, e) }
  = [ mkRule ci p grd (matchVal ci p (expr ci p x) [(EPid q, ups q) | q <- pids ci]) (annot s) ]
  -- = concat [ matchVal ci p x (EPid q) <$> ruleOfStmt ci p (sub q) | q <- pids ci ]
    where
      grd = pcGuard ci p s
      ups q = seqUpdates ci p [ incrPtrW ci p q t
                              , putMessage ci p q (e, t)
                              , nextPC ci p s
                              ]
      -- sub q = s { sndPid = EPid q }
              
-------------------------
-- ?(v :: t)
-------------------------
ruleOfStmt ci p s@Recv{ rcvMsg = (t, v) }
  = [ mkRule ci p grd (seqUpdates ci p upds) (annot s) ]
  where
    grd  = pcGuard ci p s `and`
           (readPtrR ci p t `lt` readPtrW ci p p t)
    upds = [ incrPtrR ci p t
           , getMessage ci p (v,t)
           , nextPC ci p s
           ]
    
-------------------------
-- case x of ...    
-------------------------
ruleOfStmt ci p s@Case{caseLPat = V l, caseRPat = V r}
  = [ mkRule ci p grd (matchVal ci p (expr ci p $ EVar (caseVar s)) cases) (annot s)]
  where
    grd = pcGuard ci p s
    mkLocal v = EVar (GV ("local_" ++ v))
    cases = [ (ELeft (mkLocal l), lUpdates)
            , (ERight (mkLocal r), rUpdates)
            ]
    lUpdates = seqUpdates ci p [ setState ci p [(l, expr ci p $ mkLocal l)]
                               , setPC ci p (int $ ident (caseLeft s))
                               ]
    rUpdates = seqUpdates ci p [ setState ci p [(r, expr ci p $ mkLocal r)]
                               , setPC ci p (int $ ident (caseRight s))
                               ]
-------------------------
-- nondet choice
-------------------------
ruleOfStmt ci p s@NonDet{}
  = [ mkRule ci p (grd s') (us s') (annot s) | s' <- nonDetBody s ]
  where
    grd s' = pcGuard ci p s `and`
            (nonDet ci p `eq` (int (ident s')))
    us s'  = setPC ci p (int (ident s'))

-------------------------
-- for (i < n) ...
-------------------------
ruleOfStmt ci p s@Assign { assignLhs = V v, assignRhs = e }
  = [ mkRule ci p b (seqUpdates ci p upds) (annot s) ]
  where
    b    = pcGuard ci p s
    upds = [ setState ci p [(v, expr ci p e)]
           , nextPC ci p s
           ]
    
ruleOfStmt ci p s@Iter { iterVar = V v, iterSet = set, annot = a }
  = [ mkRule ci p b    (seqUpdates ci p loopUpds) a
    , mkRule ci p notb (seqUpdates ci p exitUpds) a
    ]
  where
    b        = pcGuard ci p s `and` lt ve se
    notb     = pcGuard ci p s `and` (lneg (lt ve se))
    loopUpds = [ setPC ci p (int i) ]
    exitUpds = [ setPC ci p (int j) ]
    ve       = readState ci p v
    se       = case set of
                 S ss    -> readState ci p ss
                            -- case setBound ci set of
                            --   Just (Known _ n) -> int n
                            --   Just (Unknown _ (V x)) -> readState ci p x
                            --   Nothing -> readState ci p ss
                 SInts n -> int n
    (i, j)   = case (ident <$>) <$> cfgNext ci p (ident a) of
                 Just [i, j] -> (i, j)
                 Just [i]    -> (i, -1)
-------------------------
-- choose i in I (s)
-------------------------
ruleOfStmt ci p s@Choose { chooseVar = V v, chooseSet = set }
  = [ mkRule ci p grd (seqUpdates ci p ups) (annot s)]
  where
    grd = pcGuard ci p s
    ups = [ setPC ci p (int (ident (chooseBody s)))
          , setState ci p [(v, nonDetRange ci p set)]
          ]

-------------------------
-- assert e
-------------------------
ruleOfStmt ci p s@Assert{}
  = [ rule ci p (pcGuard ci p s) q (nextPC ci p s) ]
  where
    q = Just (pred ci p (assertPred s `pAnd` (annotPred (annot s))))

-------------------------
-- catch all
-------------------------
ruleOfStmt ci p s
  = [ mkRule ci p (pcGuard ci p s) (nextPC ci p s) (annot s) ]

ruleOfProc :: (Data a, Identable a, ILModel e)
           => ConfigInfo (PredAnnot a) -> Process (PredAnnot a) -> [Rule e]
ruleOfProc c (p, s)
  = concatMap (ruleOfStmt c p) ss
  where
    ss = listify (const True) s

rulesOfConfigInfo :: (Data a, Identable a, ILModel e)
                  => ConfigInfo (PredAnnot a) -> [Rule e]
rulesOfConfigInfo c
  = concatMap (ruleOfProc c) ps
  where
    ps = cProcs (config c)

generateModel :: ILModel e => Config () -> (ConfigInfo (PredAnnot Int), [Rule e])
generateModel c
  = (cinfo, rulesOfConfigInfo cinfo)
  where
    c' :: Config (PredAnnot ())
    c'    = annotAsserts c 
    c''   = c' {cProcs = [(p,freshStmtIds f s) | (p,s) <- cProcs c']}
    f i a = a { annotId = i }
    cinfo = mkCInfo c''
