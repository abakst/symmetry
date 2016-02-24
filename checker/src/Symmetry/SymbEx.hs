{-# Language TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, GADTs #-}
{-# Language FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing  #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language ScopedTypeVariables #-}
{-# Language ImplicitParams #-}
{-# Language ViewPatterns #-}
module Symmetry.SymbEx where

import           Prelude hiding (error, undefined)
import           Data.Generics
import           Data.Maybe
import           Data.List (nub, (\\), lookup)

import           GHC.Stack (CallStack)
import           GHC.Err.Located

import qualified Data.Map.Strict as M
import           Control.Monad.State hiding (join, get, put)
import           Symmetry.Language.AST as L
import qualified Symmetry.IL.AST       as IL

data Var a = V String
           | VIdx RMulti
           | VPtrR IL.Type
           | VPtrW IL.Type
             deriving (Ord, Eq, Show)

data Expr a where
  EVar   :: Var a -> Expr a
  EInt   :: Int -> Expr Int
  EProj1 :: Expr (a, b) -> Expr a
  EProj2 :: Expr (a, b) -> Expr b

type REnv = M.Map Role (AbsVal Int, IL.Stmt ())

envEq re1 re2
  = M.keys re1 == M.keys re2 &&
    M.foldlWithKey' check True re1
  where
    check b k (n,p) = let (n', p') = re2 M.! k in
                      p == p' && checkN n n'
    checkN :: AbsVal Int -> AbsVal Int -> Bool
    checkN (AInt x y) (AInt x' y') = (x `eqInt` x') && y == y'
    eqInt Nothing Nothing                 = True
    eqInt (Just (EVar x)) (Just (EVar y)) = x == y
    eqInt _ _                             = False

data SymbState = SymbState { renv   :: REnv
                           , ctr    :: Int
                           , ntypes :: Int
                           , me     :: (AbsVal Int, Role)
                           , renvs  :: [REnv]
                           , tyenv  :: IL.MTypeEnv
                           }
type SymbExM a = State SymbState a

stateToConfigs :: SymbState -> [IL.Config ()]
stateToConfigs state
  = map mk1Config (renvs state)
    where
      types = tyenv state
      mkVars vs = map (IL.PVar . IL.V . ("x"++) . show) [1..length vs]
      mk1Config renv
                = IL.boundAbs .
                  bigSubst $
                    IL.Config { IL.cTypes = types
                              , IL.cSets  = setBounds
                              , IL.cProcs = procs
                              , IL.cUnfold = []
                              , IL.cGlobals = globals
                              , IL.cGlobalSets = (globalSets \\ sets)
                              }
        where
          bigSubst :: IL.Config () -> IL.Config ()
          bigSubst c = everywhere (mkT goSub) c
          goSub :: IL.Set -> IL.Set
          goSub s  = maybe s (\(IL.V v) -> IL.S v) $ Data.List.lookup s setParams
          kvs   = M.toList renv
          concProcs = [ (IL.PConc n, s) | (S (RS n), (_, s)) <- kvs ]
          absProcs  = [ (roleToPid r, s) | (M r, (_, s)) <- kvs ]
          setBounds = [ IL.Known   (roleToSet r) x | (M r, (AInt _ (Just x), _)) <- kvs ]
          setParams = [ (roleToSet r, varToIL x) | (M r, (AInt (Just (EVar x)) _, _)) <- kvs ]
          sets  = [ s | (IL.PAbs _ s, _) <- absProcs ]
          procs = concProcs ++ absProcs
          globals = mapMaybe lookupType
                  . nub
                  . concatMap IL.unboundVars
                  $ map snd procs
          globalSets = nub
                     . concatMap IL.unboundSets
                     $ map snd procs
          lookupType v = something (mkQ Nothing (goType v)) procs
          goType :: IL.Var -> IL.Stmt () -> Maybe (IL.Var, IL.Type)
          goType v IL.Send{IL.sndMsg = (t,e)} = do t <- calcType v e t
                                                   return (v, t)
          goType _ _ = Nothing

calcType :: IL.Var -> IL.ILExpr -> IL.Type -> Maybe IL.Type
calcType v (IL.EVar v') t
  | v == v' = Just t
calcType v (IL.ELeft e) (IL.TSum l _)
  = calcType v e l
calcType v (IL.ERight e) (IL.TSum _ r)
  = calcType v e r
calcType v (IL.EPair e1 e2) (IL.TProd l r) =
  case t of
    Nothing -> calcType v e2 r
    _ -> t
  where
    t = calcType v e1 l
calcType _ _ _ = Nothing
                           
roleToPid :: RMulti -> IL.Pid
roleToPid r = IL.PAbs (roleIdxVar r) (roleToSet r)

roleIdxVar r = IL.GV ("i" ++ roleToString r)              

emptyState :: SymbState
emptyState = SymbState { renv = M.empty
                       , renvs = []
                       , ctr = 1
                       , ntypes = 0
                       , me = (AInt Nothing (Just 1), S (RS 0))
                       , tyenv = M.empty
                       }

runSymb :: SymbEx a -> SymbState
runSymb e = execState (runSE e) emptyState

freshInt :: SymbExM Int
freshInt = do n <- gets ctr
              modify $ \s -> s { ctr = n + 1 }
              return n

freshTId :: SymbExM Int
freshTId = do n <- gets ntypes
              modify $ \s -> s { ntypes = n + 1 }
              return n

freshVar :: SymbExM (Var a)
freshVar = (V . show) <$> freshInt

fresh :: AbsVal t -> SymbExM (AbsVal t)
fresh (AUnit _)    = AUnit . Just . EVar <$> freshVar
fresh (AInt _ n)   = (\v -> return (AInt (Just (EVar v)) n))  =<< freshVar
fresh (AString _)  = AString . Just . EVar <$> freshVar
fresh (ASum _ l r) = do v  <- Just . EVar <$> freshVar
                        i  <- freshInt
                        fl <- mapM ((setVar (V (show i)) <$>) . fresh) l
                        fr <- mapM ((setVar (V (show i)) <$>) . fresh) r
                        return $ ASum v fl fr
fresh (AProd _ l r) = do v  <- Just . EVar <$> freshVar
                         fl <- fresh l
                         fr <- fresh r
                         return $ AProd v fl fr
fresh (AList _ l)   = AList <$> (Just . EVar <$> freshVar) <*> mapM fresh l 
fresh (AArrow _ f)  = do v <- Just . EVar <$> freshVar 
                         return $ AArrow v f
fresh (APid _ p) = do v <- Just . EVar <$> freshVar
                      return $ APid v p
fresh (APidMulti _ p) = do v <- Just . EVar <$> freshVar
                           return $ APidMulti v p
fresh (ARoleSing _ p) = do v <- Just . EVar <$> freshVar
                           return $ ARoleSing v p
fresh (ARoleMulti _ p) = do v <- Just . EVar <$> freshVar
                            return $ ARoleMulti v p
fresh (AProc _ s a) = do v <- Just . EVar <$> freshVar
                         return $ AProc v s a

newtype SymbEx a = SE { runSE :: SymbExM (AbsVal a) }

data AbsVal t where
  ABot        :: AbsVal t
  APred       :: Maybe (Var Boolean) -> Maybe IL.Pred -> AbsVal Boolean
  --
  AUnit      :: Maybe (Expr ()) -> AbsVal ()
  AInt       :: Maybe (Expr Int) -> Maybe Int -> AbsVal Int
  AString    :: Maybe (Expr String) -> AbsVal String
  ASum       :: Maybe (Expr (a :+: b)) -> Maybe (AbsVal a) -> Maybe (AbsVal b) -> AbsVal (a :+: b)
  AProd      :: Maybe (Expr (a,b)) -> AbsVal a -> AbsVal b -> AbsVal (a, b)
  AList      :: Maybe (Expr [a]) -> Maybe (AbsVal a) -> AbsVal [a]
  AArrow     :: Maybe (Expr (a -> b)) -> (AbsVal a -> SymbEx b) -> AbsVal (a -> b)
  APid       :: Maybe (Expr (Pid RSing)) -> L.Pid (Maybe RSing) -> AbsVal (Pid RSing)
  APidElem   :: Maybe (Expr (Pid RMulti)) -> Maybe (Var Int) -> L.Pid (Maybe RMulti) -> AbsVal (Pid RSing)
  APidMulti  :: Maybe (Expr (Pid RMulti)) -> L.Pid (Maybe RMulti) -> AbsVal (Pid RMulti)
  ARoleSing  :: Maybe (Expr RSing) -> RSing -> AbsVal RSing
  ARoleMulti :: Maybe (Expr RMulti) -> RMulti -> AbsVal RMulti
  AProc      :: Maybe (Expr (Process SymbEx a)) -> IL.Stmt () -> AbsVal a -> AbsVal (Process SymbEx a)

-- instance Show (AbsVal t) where
--   show (AUnit _) = "AUnit"
--   show (AInt _ _) = "AInt"
--   show (AString _) = "AString"
--   show (ASum _ l r) = show l ++ "+" ++ show r
--   show (AProd _ l r) = show l ++ "*" ++ show r
--   show (APid x p) = show p ++ "@" ++ show x 

setVar :: Var t -> AbsVal t -> AbsVal t                
setVar v = setExpr (EVar v)

setExpr :: Expr t -> AbsVal t -> AbsVal t
setExpr e (AUnit _)       = AUnit (Just e)
setExpr e (AString _)     = AString (Just e)
setExpr e (AInt _ i)      = AInt  (Just e) i
setExpr e (ASum _ l r)    = ASum  (Just e) l r
setExpr e (APid _ p)      = APid  (Just e) p
setExpr e (AProd _ p1 p2) = AProd (Just e) p1 p2

getVar :: AbsVal t -> Maybe (Expr t)
getVar (AUnit v)     = v
getVar (AString v)   = v
getVar (AInt v _)    = v
getVar (ASum v _ _)  = v
getVar (AProd v _ _) = v
getVar (APid v _)    = v

absToType :: Typeable t => AbsVal t -> IL.Type
absToType x = go (typeRep x)
  where
    go :: TypeRep -> IL.Type
    go a
      | tyConName (typeRepTyCon a) == "()"
        = IL.TUnit
      | tyConName (typeRepTyCon a) == "Pid" &&
        "RSing" == (tyConName . typeRepTyCon $ head as)
        = IL.TPid
      | tyConName (typeRepTyCon a) == "Pid" &&
        "RMulti" == (tyConName . typeRepTyCon $ head as)
        = IL.TPid -- probably not right
      | tyConName (typeRepTyCon a) == "[]" &&
        tyConName (typeRepTyCon $ head as) == "Char"
        = IL.TString
      | tyConName (typeRepTyCon a) == "[]"
        = error "TBD: IL List" 
      | tyConName (typeRepTyCon a) == "Either"
        = IL.TSum (go (head as)) (go (as !! 1))
      | tyConName (typeRepTyCon a) == "(,)"
        = IL.TProd (go (head as)) (go (as !! 1))
      | tyConName (typeRepTyCon a) == "Int"
        = IL.TInt
      | otherwise
        = error "TBD: absToType" 
      where
        as = typeRepArgs a

-------------------------------------------------
-- | Recv t tells us how to create a default abstraction of type t
-------------------------------------------------
instance Pat SymbEx where
  joinPat x y = SE $ do xx <- runSE x
                        yy <- runSE y
                        return $ xx `join` yy

  liftPat1 x  = SE $ do xx <- runSE x
                        return $ ASum Nothing (Just xx) Nothing

  liftPat2 x  = SE $ do xx <- runSE x
                        return $ ASum Nothing Nothing (Just xx)

instance ArbPat SymbEx () where            
  arb = SE . return $ AUnit Nothing

instance ArbPat SymbEx Int where            
  arb = SE . fresh $ AInt Nothing Nothing

instance {-# OVERLAPPING #-} ArbPat SymbEx String where            
  arb = SE . return $ AString Nothing

instance ArbPat SymbEx (Pid RSing) where            
  arb = SE . return $ APid Nothing (Pid Nothing)

instance ArbPat SymbEx (Pid RMulti) where            
  arb = SE . return $ APidMulti Nothing (Pid Nothing)

instance {-# OVERLAPPABLE #-} ArbPat SymbEx a => ArbPat SymbEx [a] where
  arb = SE $ do a <- runSE arb
                return $ AList Nothing (Just a)

-------------------------------------------------
-- | An instance of Send t means that t can be sent in a message
-------------------------------------------------
class (Typeable a) => Send a where
  -- This line intentionally left blank

instance Send (()) where
instance Send (Int) where
instance Send (String) where
instance (Send a, Send b) => Send (a :+: b) where
instance (Send a, Send b) => Send (a,b) where
instance Send (Pid RSing) where

-------------------------------------------------
-- | "Pure" values i.i. not Process values
-------------------------------------------------
class Pure t where
  -- This line intentionally left blank

instance Pure (()) where
instance Pure (Int) where
instance Pure (String) where
instance (Pure a, Pure b) => Pure (a :+: b) where
instance (Pure a, Pure b) => Pure (a,b) where
instance Pure (Pid RSing) where

-------------------------------------------------
-- | How to join abstractions
-------------------------------------------------
-- class Join t where
--   join :: AbsVal t -> AbsVal t -> AbsVal t

join :: (?callStack :: CallStack)
     => AbsVal t -> AbsVal t -> AbsVal t          

join ABot x = x
join x    ABot = x

join (AUnit _) (AUnit _)      = AUnit Nothing
join (AInt _ _)  (AInt _ _)   = AInt Nothing Nothing
join (AString _)  (AString _) = AString Nothing
join (AList _ a) (AList _ b)  = AList Nothing (a `maybeJoin` b)

join (APid _ (Pid Nothing)) (APid _ _) = APid Nothing (Pid Nothing)
join (APid _ _) (APid _ (Pid Nothing)) = APid Nothing (Pid Nothing)
join (APid _ _) (APid _ _)             = error "Join Pid RSing: TBD"

join (AProc _ s1 a1) (AProc _ s2 a2)
  = AProc Nothing (s1 `joinStmt` s2) (a1 `join` a2)

join (ASum _ l1 r1) (ASum _ l2 r2)
  = ASum Nothing (l1 `maybeJoin` l2) (r1 `maybeJoin` r2)

join (AProd _ l1 r1) (AProd _ l2 r2)
  = AProd Nothing (l1`join`l2) (r1`join`r2)

maybeJoin :: forall a.
             Maybe (AbsVal a)
          -> Maybe (AbsVal a)
          -> Maybe (AbsVal a)
maybeJoin (Just x) (Just y) = Just (x `join` y)
maybeJoin (Just x) Nothing  = Just x
maybeJoin _  y              = y

-------------------------------------------------
-- | Helpers for generating IL from AbsValtractions
-------------------------------------------------
joinStmt :: IL.Stmt () -> IL.Stmt () -> IL.Stmt ()
joinStmt (IL.NonDet ss1 _) (IL.NonDet ss2 _)
  = IL.NonDet (ss1 ++ ss2) ()
joinStmt (IL.NonDet ss _) s
  = IL.NonDet (s : ss) ()
joinStmt s (IL.NonDet ss _)
  = IL.NonDet (s : ss) ()
joinStmt s1 s2
  = IL.NonDet [s1, s2] ()

varToIL :: Var a -> IL.Var
varToIL (V x)     = IL.V ("x" ++ x)
varToIL (VPtrR x) = IL.VPtrR x
varToIL (VPtrW x) = IL.VPtrW x
varToIL (VIdx r)  = roleIdxVar r

varToILSet :: Var a -> IL.Set
varToILSet (V x) = IL.S ("x" ++ x)

varToILSetVar :: Var a -> IL.Set
varToILSetVar (V x) = IL.SV ("x" ++ x)

pidAbsValToIL :: (?callStack :: CallStack)
              => AbsVal (Pid RSing) -> IL.ILExpr
pidAbsValToIL (APid Nothing (Pid (Just (RS r)))) = IL.EPid (IL.PConc r)
pidAbsValToIL (APid (Just (EVar x)) _) = IL.EVar (varToIL x)
-- Oy
pidAbsValToIL (APid Nothing (Pid (Just (RSelf (S (RS r)))))) = IL.EPid (IL.PConc r)
pidAbsValToIL _                 = error "pidAbsValToIL: back to the drawing board "


-- mkVal :: String -> [IL.Pid] -> IL.ILExpr
-- mkVal s = IL.MTApp (IL.MTyCon s)

absExpToIL :: (?callStack :: CallStack)
           => Expr a -> IL.ILExpr
absExpToIL (EVar x)   = IL.EVar (varToIL x)
absExpToIL (EProj1 e) = IL.EProj1 (absExpToIL e)
absExpToIL (EProj2 e) = IL.EProj2 (absExpToIL e)

absToIL :: (?callStack :: CallStack)
        => AbsVal a -> [IL.ILExpr]
absToIL ABot          = error "TBD: absToIL ABot"
absToIL (AArrow _ _)  = error "TBD: absToIL AArrow"
absToIL (ARoleSing _ _)  = error "TBD: absToIL ARoleSing"
absToIL (ARoleMulti _ _)  = error "TBD: absToIL ARoleMulti"

absToIL (AUnit _)          = [IL.EUnit]
absToIL (AInt (Just e) _)  = [absExpToIL e]
absToIL (AInt  _ (Just i)) = [IL.EInt i]
absToIL (AString _)        = [IL.EString]
absToIL (AList _ _)        = error "TBD: absToIL List"

absToIL (APidElem Nothing (Just i) (Pid (Just r)))
  = [IL.EPid (IL.PAbs (varToIL i) (roleToSet r))]

absToIL (APid (Just x) _) = [absExpToIL x]
absToIL (APid Nothing (Pid (Just (RS r))))             = [IL.EPid (IL.PConc r)]
absToIL (APid Nothing (Pid (Just (RSelf (S (RS r)))))) = [IL.EPid (IL.PConc r)]
absToIL (APid Nothing (Pid (Just (RSelf (M r)))))      = [IL.EPid (roleToPid r)]
absToIL (APid Nothing (Pid (Just (RElem (RM r)))))     = error "TBD: elem"
absToIL (APid Nothing (Pid Nothing))                   = error "wut"

absToIL (APidMulti (Just x) _)              = error "TBD: PidMulti" 
absToIL (APidMulti Nothing (Pid (Just r)))  = error "TBD: PidMulti" 

absToIL (ASum (Just x) _ _) = [absExpToIL x]
absToIL (ASum _ (Just a) Nothing)  = IL.ELeft <$> absToIL a
absToIL (ASum _ Nothing (Just b))  = IL.ERight <$> absToIL b
-- absToIL (ASum (Just x) (Just a) (Just b))
--   = (IL.MCaseL (IL.VL (varToIL x)) <$> absToIL a) ++ 
--     (IL.MCaseR (IL.VL (varToIL x)) <$> absToIL b)
absToIL (ASum Nothing (Just a) (Just b))
  = (IL.ELeft <$> absToIL a) ++ (IL.ERight <$> absToIL b)
absToIL (ASum _ _ _)   = error "absToIL sum"

absToIL (AProd (Just x) _ _) = [absExpToIL x]
absToIL (AProd _ a b) = do x <- absToIL a
                           y <- absToIL b
                           return $ IL.EPair x y

absToIL (APred _ _) = error "absToIL APred"
-------------------------------------------------
-- | Generate IL from primitive Processes
-------------------------------------------------
absPidToExp :: (?callStack :: CallStack)
            => AbsVal (Pid RSing) -> IL.ILExpr
absPidToExp p = let [e] = absToIL p in e

sendToIL :: (?callStack :: CallStack)
         => (Typeable a) => AbsVal (Pid RSing) -> AbsVal a -> SymbExM (IL.Stmt ())
sendToIL p m = do
  let t     = absToType m
  case [ (t, e) | e <- absToIL m ] of
    [s] -> choosePid p $ mkSend s
    ss  -> choosePid p (\p -> IL.NonDet (map (`mkSend` p) ss) ())
  where
    mkSend msg p         = IL.Send p msg ()
  -- case IL.lookupType g t of
  --   Just i  -> nonDetSends i g cs p
  --   Nothing -> do i <- freshTId
  --                 let g' = M.insert i t g
  --                 modify $ \s -> s { tyenv = g' }
  --                 nonDetSends i g' cs p
  -- where
  --   sends :: Int -> IL.MTypeEnv -> [IL.MConstr] -> [IL.Pid -> IL.Stmt ()]
  --   sends i g cs       = map (mkSend . lkupMsg i g) cs
  --   nonDetSends i g cs p = case sends i g cs of
  --                            [s] -> choosePid p s
  --                            ss  -> choosePid p (\p -> IL.NonDet (map ($ p) ss) ())

choosePid :: (?callStack :: CallStack)
          => AbsVal (Pid RSing) -> (IL.ILExpr -> IL.Stmt ()) -> SymbExM (IL.Stmt ())
choosePid p@(APid _ (Pid (Just (RElem r)))) f
  = do v <- freshVar
       let pv = IL.EPid (IL.PAbs (varToIL v) (roleToSet r))-- IL.EVar (varToIL v)
       return $ IL.Choose (varToIL v) (roleToSet r) (f pv) ()
choosePid p s
  = return (s (absPidToExp p))
          

recvToIL :: (?callStack :: CallStack)
         => (Typeable a) => AbsVal a -> Var a -> SymbExM (IL.Stmt ())
recvToIL m x = do
  let t   = absToType m
  return (IL.Recv (t, varToIL x) ())
--   case IL.lookupType g t of
--     Just i  -> return $ nonDetRecvs i g cs
--     Nothing -> do i <- freshTId
--                   let g' = M.insert i t g
--                   modify $ \s -> s { tyenv = g' }
--                   return $ nonDetRecvs i g' cs
--   where
--     recvs i g cs       = map (flip IL.Recv () . lkupMsg i g) cs
--     nonDetRecvs i g cs = case recvs i g cs of
--                            [r] -> r
--                            rs  -> IL.NonDet rs ()
                   
-- lkupMsg i g c  = (i, lkup i g c, c)
--   where
--     lkup i g c   = fromMaybe (error ("recv:" ++ show c)) $ IL.lookupConstr (g M.! i) c

skip :: IL.Stmt ()
skip = IL.Skip ()

assign :: Var a -> IL.ILExpr -> IL.Stmt ()
assign v e
  = IL.Assign (varToIL v) e ()
-------------------------------------------------
-- | Sequence Statements
-------------------------------------------------
seqStmt :: IL.Stmt () -> IL.Stmt () -> IL.Stmt ()

seqStmt (IL.Skip _) s = s
seqStmt s (IL.Skip _) = s

seqStmt (IL.Block ss _) (IL.Block ss' _) = IL.Block (ss ++ ss') ()

seqStmt s (IL.Block ss _) = IL.Block (s : ss) ()
seqStmt (IL.Block ss _) s = IL.Block (ss ++ [s]) ()

seqStmt s1 s2 = IL.Block [s1, s2] ()

-------------------------------------------------
-- | Updates to roles
-------------------------------------------------
insRoleM :: (?callStack :: CallStack)
         => Role -> AbsVal Int -> SymbEx (Process SymbEx a) -> SymbExM ()
insRoleM k n p = do m <- gets renv
                    case M.lookup k m of
                      Nothing -> do
                        oldMe <- gets me
                        modify $ \s -> s { me = (n, k) }
                        AProc _ st _ <- runSE p
                        modify $ \s -> s { renv = M.insert k (n, st) (renv s), me = oldMe }
                      Just _  ->
                        error $ "insRoleM attempting to spawn already spawned role" ++ show k

symSpawnSingle :: (?callStack :: CallStack)
               => SymbEx RSing
               -> SymbEx (Process SymbEx a)
               -> SymbEx (Process SymbEx (Pid RSing))
symSpawnSingle r p = SE $ do (ARoleSing _ r'@(RS j)) <- runSE r
                             meCtxt <- gets me
                             case meCtxt of
                               (_, S (RSelf (S _))) -> do 
                                 insRoleM (S r') (AInt Nothing (Just 1)) p
                                 return $ AProc Nothing skip (APid Nothing (Pid (Just r')))
                               (_, S (RS _))        -> do
                                 insRoleM (S r') (AInt Nothing (Just 1)) p
                                 return $ AProc Nothing skip (APid Nothing (Pid (Just r')))
                               (n, _)               -> do
                                 m <- gets renv
                                 let r'' = RM j
                                 when (isJust (M.lookup (M r'') m)) err
                                 insRoleM (M r'') n p
                                 return $ AProc Nothing skip (APid Nothing (Pid (Just (RElem r''))))
  where
    err = error "Attempting to spawn already spawned role"

symSpawnMany :: (?callStack :: CallStack)
             => SymbEx RMulti
             -> SymbEx Int
             -> SymbEx (Process SymbEx a)
             -> SymbEx (Process SymbEx (Pid RMulti))
symSpawnMany r n p = SE $ do (ARoleMulti _ r') <- runSE r
                             a                 <- runSE n
                             (k, _)            <- gets me
                             let num = case k of
                                         AInt _ (Just 1) -> a
                                         _               -> AInt Nothing Nothing
                             insRoleM (M r') num p
                             return $ AProc Nothing skip (APidMulti Nothing (Pid (Just r')))

-------------------------------------------------
-- | The Symbolic Execution
-------------------------------------------------

-------------------------------------------------
symtt :: SymbEx ()
-------------------------------------------------
symtt
  = SE . return $ AUnit Nothing

-------------------------------------------------
symInt :: Int -> SymbEx Int
-------------------------------------------------
symInt n
  = SE . fresh $ AInt Nothing (Just n)

-------------------------------------------------
symStr :: String -> SymbEx String
-------------------------------------------------
symStr _
  = SE . return $ AString Nothing

-------------------------------------------------
symBool :: Boolean -> SymbEx Boolean
-------------------------------------------------
symBool b
  = SE $ do u <- runSE symtt
            return $ case b of
                       Left _ -> 
                         ASum Nothing (Just u) Nothing
                       Right _ -> 
                         ASum Nothing Nothing (Just u) 

-------------------------------------------------
symPlus :: SymbEx Int -> SymbEx Int -> SymbEx Int
-------------------------------------------------
symPlus _ _ = arb

symNeg :: SymbEx Int -> SymbEx Int
symNeg _ = arb

-------------------------------------------------
symEq :: Eq a
      => SymbEx a
      -> SymbEx a
      -> SymbEx Boolean
-------------------------------------------------
symEq a b  = SE $ do av <- runSE a
                     bv <- runSE b
                     return $ APred Nothing (Just (opPred IL.Eq av bv))

opPred :: IL.Op -> AbsVal a -> AbsVal a -> IL.Pred
opPred o (AInt _ (Just i)) (AInt _ (Just j))
  = IL.ILBop o (IL.EInt i) (IL.EInt j)
opPred o (AInt (Just x) _) (AInt _ (Just i))
  = IL.ILBop o (IL.EInt i) (absExpToIL x)
opPred o (AInt _ (Just i)) (AInt (Just x) _)
  = IL.ILBop o (IL.EInt i) (absExpToIL x)
opPred o (AInt (Just x) _) (AInt (Just y) _)
  = IL.ILBop o (absExpToIL x) (absExpToIL y)
opPred _ _ _
  = undefined

-------------------------------------------------
symGt, symLt :: SymbEx Int
             -> SymbEx Int
             -> SymbEx Boolean
-------------------------------------------------
symGt x y
  = SE $ do xv <- runSE x
            yv <- runSE y
            return $ APred Nothing (Just (opPred IL.Gt xv yv))
symLt x y
  = SE $ do xv <- runSE x
            yv <- runSE y
            return $ APred Nothing (Just (opPred IL.Lt xv yv))


-------------------------------------------------
symNot :: SymbEx Boolean
       -> SymbEx Boolean
-------------------------------------------------
symNot b   = SE $ do v <- runSE b
                     return $ case v of
                                APred Nothing Nothing ->
                                  APred Nothing Nothing
                                APred Nothing (Just p) ->
                                  APred Nothing (Just (IL.ILNot p))
                                _ ->
                                  error "TBD: symNot"

-------------------------------------------------
symAnd, symOr :: SymbEx Boolean
              -> SymbEx Boolean
              -> SymbEx Boolean
-------------------------------------------------
symAnd p q
  = SE $ do pp <- runSE p 
            qq <- runSE q
            case (pp, qq) of
              (APred _ (Just e1), APred _ (Just e2)) ->
                return $ APred Nothing (Just (IL.ILAnd e1 e2))
              _ -> runSE arb
symOr  p q
  = SE $ do pp <- runSE p 
            qq <- runSE q
            case (pp, qq) of
              (APred _ (Just e1), APred _ (Just e2)) ->
                return $ APred Nothing (Just (IL.ILOr e1 e2))
              _ -> runSE arb

-------------------------------------------------
symLam :: (SymbEx a -> SymbEx b) -> SymbEx (a -> b)
-------------------------------------------------
symLam f
  = SE . return . AArrow Nothing $ \a -> f (SE $ return a)

-------------------------------------------------
symApp :: SymbEx (a -> b) -> SymbEx a -> SymbEx b
-------------------------------------------------
symApp e1 e2
  = SE $ do AArrow _ f' <- runSE e1
            e2'         <- runSE e2
            runSE (f' e2')

-------------------------------------------------
-- Lists
-------------------------------------------------
symNil :: SymbEx [a]
symNil
  = SE . return $ AList Nothing Nothing

symCons :: SymbEx a -> SymbEx [a] -> SymbEx [a]
symCons x l
  = SE $ do xv          <- runSE x
            AList _ xv' <- runSE l
            return $ case xv' of
                       Nothing  -> AList Nothing (Just xv)
                       Just xv' -> AList Nothing (Just $ xv `join` xv')

symMatchList :: forall a b.
               (?callStack :: CallStack, Typeable a, ArbPat SymbEx a)
             => SymbEx [a]
             -> SymbEx (() -> b)
             -> SymbEx ((a, [a]) -> b)
             -> SymbEx b         
symMatchList l nilCase consCase
  = SE $ do nilv  <- runSE (app nilCase tt)
            lv    <- runSE l
            case lv of
              AList _ (Just v) -> do
                      v <- runSE arb
                      let tl = SE . return $ AList Nothing (Just v)
                      cv <- runSE $ symApp consCase (pair (SE . return $ v) tl)
                      return (cv `join` nilv)
              AList _ Nothing  -> return nilv

-------------------------------------------------
symAssert :: SymbEx Boolean -> SymbEx (Process SymbEx ())
-------------------------------------------------
symAssert exp
  = SE $ do bool <- runSE exp
            case bool of
              APred _ (Just e) -> return $ AProc Nothing (assert e) (AUnit Nothing)
  where
    assert e = IL.Assert { IL.assertPred = e, IL.annot = () }

-------------------------------------------------
symReadPtrR :: Typeable a => SymbEx a -> SymbEx (Process SymbEx Int)
-------------------------------------------------
symReadPtrR v
  = SE $ do t  <- absToType <$> runSE v
            v' <- freshVar
            return $ AProc Nothing (assign v' (IL.EVar $ IL.VPtrR t))
                   $ AInt (Just (EVar v')) Nothing

-------------------------------------------------
symReadPtrW :: Typeable a => SymbEx a -> SymbEx (Process SymbEx Int)
-------------------------------------------------
symReadPtrW v
  = SE $ do t  <- absToType <$> runSE v
            v' <- freshVar
            return $ AProc Nothing (assign v' (IL.EVar $ IL.VPtrW t))
                   $ AInt (Just (EVar v')) Nothing

-------------------------------------------------
symReadIdx :: SymbEx (Process SymbEx Int)
-------------------------------------------------
symReadIdx
  = SE $ do (_, M r) <- gets me
            return $ AProc Nothing skip $ AInt (Just . EVar $ VIdx r) Nothing

-------------------------------------------------
symReadGhost :: SymbEx (Pid r) -> String -> SymbEx (Process SymbEx Int)
-------------------------------------------------
symReadGhost p s
  = SE $ do v <- freshVar
            [IL.EPid pid] <- absToIL <$> runSE p
            return $ AProc Nothing (assign v (IL.EVar (IL.VRef pid ("x" ++ s))))
                   $ AInt (Just (EVar v)) Nothing

-------------------------------------------------
symSelf :: SymbEx (Process SymbEx (Pid RSing))
-------------------------------------------------
symSelf
  = SE $ do (_, r) <- gets me
            return . AProc Nothing skip $ APid Nothing (Pid (Just (RSelf r)))

-------------------------------------------------
symRet :: SymbEx a -> SymbEx (Process SymbEx a)
-------------------------------------------------
symRet x
  = SE $ do a <- runSE x
            return (AProc Nothing skip a)
-------------------------------------------------
symBind :: SymbEx (Process SymbEx a) -> SymbEx (a -> Process SymbEx b) -> SymbEx (Process SymbEx b)
-------------------------------------------------
symBind mm mf
  = SE $ do AProc _ st a  <- runSE mm
            AArrow _ f <- runSE mf
            AProc _ st' b <- runSE $ f a
            return $ AProc Nothing (st `seqStmt` st') b

-------------------------------------------------
symForever :: (?callStack :: CallStack)
           => SymbEx (Process SymbEx ()) -> SymbEx (Process SymbEx ())
-------------------------------------------------
symForever p
  = SE $ do n <- freshInt
            let v  = IL.LV $ "endL" ++ show n
                sv = IL.Goto v ()
            AProc b s r <- prohibitSpawn (runSE p)
            return $ AProc b (IL.Loop v (s `seqStmt` sv) ()) r

-------------------------------------------------
symFixM :: (?callStack :: CallStack)
        => SymbEx ((a -> Process SymbEx a) -> a -> Process SymbEx a)
        -> SymbEx (a -> Process SymbEx a)
-------------------------------------------------
symFixM f
  = SE . return . AArrow Nothing $ \a ->
          SE $ do n <- freshInt
                  let v = IL.LV $ "L" ++ show n
                      sv = IL.Goto v  ()
                      g = SE . return . AArrow Nothing $ \a -> SE $ return (AProc Nothing sv a)
                  AArrow _ h  <- runSE (app f g)
                  AProc b s r <- prohibitSpawn $ runSE (h a)
                  return $ AProc b (IL.Loop v s ()) r

prohibitSpawn m
  = do env <- gets renv
       r    <- m
       env' <- gets renv
       unless (envEq env env') err
       return r
err
  = error "Spawning inside a loop prohibited! Use SpawnMany instead"
-------------------------------------------------
symNewRSing :: SymbEx (Process SymbEx RSing)
-------------------------------------------------
symNewRSing
  = SE $ do n <- freshInt
            return (AProc Nothing skip (ARoleSing Nothing (RS n)))

-------------------------------------------------
symNewRMulti :: SymbEx (Process SymbEx RMulti)
-------------------------------------------------
symNewRMulti
  = SE $ do n <- freshInt
            return (AProc Nothing skip (ARoleMulti Nothing (RM n)))

-------------------------------------------------
symDoN :: String
       -> SymbEx Int
       -> SymbEx (Int -> Process SymbEx a)
       -> SymbEx (Process SymbEx [a])
-------------------------------------------------
symDoN s n f
  = SE $ do let v = V s
            AInt x nv <- runSE n
            AArrow _ g <- runSE f
            AProc _ s _ <- runSE (g (AInt (Just (EVar v)) Nothing))
            return $ AProc Nothing (iter v x nv s) (error "TBD: symDoN")
    where
      incrVar v = (`seqStmt` incr v)
      iter v _ (Just n) s = IL.Iter (varToIL v) (IL.SInts n) (incrVar v s) ()
      iter v (Just (EVar x)) _ s = IL.Iter (varToIL v) (varToILSet x) (incrVar v s) ()
      iter (V x) _ _ s    =
                  let v = IL.LV $ "L" ++ show x
                      sv = IL.Goto v  ()
                  in IL.Loop v ((s `seqStmt` sv) `joinStmt` skip) ()

incr x = IL.Assign (varToIL x) (IL.EPlus (IL.EVar (varToIL x)) (IL.EInt 1)) ()

-------------------------------------------------
symLookup :: SymbEx (Pid RMulti)
          -> SymbEx Int
          -> SymbEx (Pid RSing)
-------------------------------------------------
symLookup p i
  = SE $ do APidMulti _ (Pid (Just r)) <- runSE p
            AInt _ _                   <- runSE i
            return $ APid Nothing (Pid (Just (RElem r)))
                   

-------------------------------------------------
symDoMany :: String
          -> SymbEx (Pid RMulti)
          -> SymbEx (Pid RSing -> Process SymbEx a)
          -> SymbEx (Process SymbEx [a])
-------------------------------------------------
symDoMany s p f
  = SE $ do APidMulti x pid {- (Pid (Just r)) -} <- runSE p
            AArrow _ g                 <- runSE f
            -- v <- freshVar
            let v = V s
            case (x, pid) of
              (_, Pid (Just r)) -> do
                AProc _ s _  <- runSE (g (APidElem Nothing (Just v) (Pid (Just r))))
                return $ AProc Nothing (iter v r s) (error "TBD: symDoMany")
              (Just (EVar x), _) -> do
                AProc _ s _  <- runSE (g (APidElem (Just (EVar x)) (Just v) (Pid Nothing)))
                return $ AProc Nothing (iterVar v x s) (error "TBD: symDoMany")
    where
      incrVar v = (`seqStmt` incr v)
      iter v r s    = IL.Iter (varToIL v) (roleToSet r) (incrVar v s) ()
      iterVar v x s = IL.Iter (varToIL v) (varToILSetVar x) (incrVar v s) ()

roleToSet :: RMulti -> IL.Set
roleToSet r = IL.S $ roleToString r

roleToString :: RMulti -> String
roleToString (RM n) = "r" ++ show n                   
-------------------------------------------------
symExec :: SymbEx (Process SymbEx a)
        -> SymbEx a
-------------------------------------------------
symExec p
  = SE $ do (AProc _ st a) <- runSE p
            modify $ \s -> s { renv  = M.empty
                             , renvs = M.insert (snd $ me s) (AInt Nothing (Just 1), st) (renv s) : renvs s
                             }
            return a

-------------------------------------------------
symRecv :: (?callStack :: CallStack, Typeable a, ArbPat SymbEx a)
        => SymbEx (Process SymbEx a)
-------------------------------------------------
symRecv
  = SE $ do v     <- freshVal
            x     <- freshVar
            let val = setVar x v
            s     <- recvToIL val x
            return $ AProc Nothing s val

freshVal :: ArbPat SymbEx a => SymbExM (AbsVal a)
freshVal = runSE arb >>= fresh

-------------------------------------------------
symSend :: (?callStack :: CallStack, Typeable a)
        => SymbEx (Pid RSing)
        -> SymbEx a
        -> SymbEx (Process SymbEx ())
-------------------------------------------------
symSend pidM mM
  = SE $ do p <- runSE pidM
            m <- runSE mM
            s <- sendToIL p m
            return (AProc Nothing s (AUnit Nothing))
-------------------------------------------------
symDie :: SymbEx (Process SymbEx a)
-------------------------------------------------
symDie 
  = SE $ return (AProc Nothing s ABot)
    where
      s = IL.Die ()

symInL :: SymbEx a
       -> SymbEx (a :+: b)
symInL a = SE $ do av <- runSE a
                   return $ ASum Nothing (Just av) Nothing
symInR :: SymbEx b
       -> SymbEx (a :+: b)
symInR b = SE $ do bv <- runSE b
                   return $ ASum Nothing Nothing (Just bv)

symMatch :: forall a b c.
            (?callStack :: CallStack,
             Typeable a, Typeable b, ArbPat SymbEx a, ArbPat SymbEx b) =>
            SymbEx (a :+: b)
         -> SymbEx (a -> c)
         -> SymbEx (b -> c)
         -> SymbEx c
symMatch s l r
  = SE $ do sum <- runSE s
            symMatchSum sum l r

symMatchSum :: forall a b c.
               (?callStack :: CallStack, Typeable a, Typeable b, ArbPat SymbEx a, ArbPat SymbEx b) =>
               AbsVal (a :+: b)
            -> SymbEx (a -> c)
            -> SymbEx (b -> c)
            -> SymbExM (AbsVal c)
symMatchSum (ASum x vl vr) l r
  = case (vl, vr) of
      (Just a, Nothing) -> runSE . app l . SE $ return a
      (Nothing, Just b) -> runSE . app r . SE $ return b
      (Nothing, Nothing) -> do
        (v1, v2) <- case x of
                      Nothing -> error "does this happen?" -- return (Nothing, Nothing)
                      _       -> do i  <- freshInt -- instead of freshVar to reuse var in diff. branch
                                    return (V (show i), V (show i))
        val1 <- setVar v1 <$> runSE arb
        val2 <- setVar v2 <$> runSE arb
        c1 <- runSE . app l . SE . return $ val1
        c2 <- runSE . app r . SE . return $ val2
        return $ joinProcs x (Just (EVar v1)) (Just (EVar v2)) c1 c2
      (Just a, Just b)  -> do 
        c1 <- runSE . app l . SE . return $ a
        c2 <- runSE . app r . SE . return $ b
        case x of
          Nothing -> 
            return $ joinProcs Nothing (getVar a) (getVar b) c1 c2
          Just v -> 
            return $ joinProcs (Just v) (getVar a) (getVar b) c1 c2

joinProcs :: forall a b x y.
             (?callStack :: CallStack)
          => Maybe (Expr b) -> Maybe (Expr x) -> Maybe (Expr y) -> AbsVal a -> AbsVal a -> AbsVal a
-- TODO: handle other expressions
joinProcs (Just (EVar x)) (Just (EVar x1)) (Just (EVar x2)) (AProc _ s1 v1) (AProc _ s2 v2)
  = AProc Nothing (IL.Case (varToIL x) (varToIL x1) (varToIL x2) s1 s2 ()) (v1 `join` v2)
joinProcs _ _ _ t1 t2
  = t1 `join` t2

symPair :: SymbEx a
        -> SymbEx b
        -> SymbEx (a, b)
symPair a b
  = SE $ do av <- runSE a
            bv <- runSE b
            return $ AProd Nothing av bv

symProj1 :: SymbEx (a, b)
         -> SymbEx a
symProj1 p = SE $ do p' <- runSE p
                     case p' of
                       AProd (Just e) a _ ->
                         return (setExpr (EProj1 e) a)
                       AProd _ a _        -> return a

symProj2 :: SymbEx (a, b)
         -> SymbEx b
symProj2 p = SE $ do p' <- runSE p
                     case p' of
                       AProd (Just e) _ b ->
                         return (setExpr (EProj2 e) b)
                       AProd _ _ b -> return b

-------------------------------------------------
-- Instances
-------------------------------------------------
instance Symantics SymbEx where
  data Process SymbEx a = P a
  -- Base Types
  tt        = symtt
  int       = symInt
  str       = symStr
  bool      = symBool

  -- Base Type Operations            
  plus      = symPlus
  neg       = symNeg
  eq        = symEq
  gt        = symGt
  lt        = symLt
  not       = symNot
  and       = symAnd 
  or        = symOr

  -- Lists
  nil       = symNil
  cons      = symCons

  lam       = symLam
  app       = symApp
  self      = symSelf
  bind      = symBind
  fixM      = symFixM
  spawn     = symSpawnSingle
  spawnMany = symSpawnMany
  exec      = symExec
  ret       = symRet
  newRSing  = symNewRSing
  newRMulti = symNewRMulti
  doMany    = symDoMany
  lookup    = symLookup
  doN       = symDoN
  die       = symDie
  forever   = symForever

  inl   = symInL
  inr   = symInR
  pair  = symPair
  proj1 = symProj1
  proj2 = symProj2

  recv = symRecv
  send = symSend

  match = symMatch
  matchList = symMatchList

  readGhost = symReadGhost
  assert    = symAssert
  readPtrR  = symReadPtrR
  readPtrW  = symReadPtrW
  readMyIdx = symReadIdx
