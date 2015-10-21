{-# Language TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, GADTs #-}
{-# Language FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing  #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language ScopedTypeVariables #-}
module Symmetry.SymbEx where

import           Data.List (nub)
import           Data.Tuple (swap)
import           Data.Generics
import           Data.Typeable
import           Data.Maybe

import           Data.Hashable
import qualified Data.Map.Strict as M
import           Control.Monad.State hiding (join, get, put)
import           Symmetry.Language.AST as L
import qualified Symmetry.IL.AST       as IL

import           Control.Applicative ((<$>))

data Var a = V Int deriving (Ord, Eq, Show)

type REnv = M.Map Role (IL.Stmt ())
data Role = S RSing
          | M RMulti
            deriving (Ord, Eq, Show)

instance Hashable Role where
  hashWithSalt s (S r) = hashWithSalt s r
  hashWithSalt s (M r) = hashWithSalt s r

data SymbState = SymbState { renv   :: REnv
                           , ctr    :: Int
                           , ntypes :: Int
                           , me     :: Role
                           , renvs  :: [REnv]
                           , tyenv  :: IL.MTypeEnv
                           }
type SymbExM a = State SymbState a

stateToConfigs :: SymbState -> [IL.Config ()]
stateToConfigs state
  = map mk1Config (renvs state)
    where
      types = tyenv state
      mkVars vs = map (IL.PVar . IL.V . ("x_"++) . show) [1..length vs]
      mk1Config renv
                = IL.Config { IL.cTypes = types
                            , IL.cSets  = sets
                            , IL.cProcs = procs
                            , IL.cUnfold = []
                            }
        where
          kvs   = M.toList renv
          concProcs = [ (IL.PConc n, s) | (S (RS n), s) <- kvs ]
          absProcs  = [ (IL.PAbs (IL.V "i") (roleToSet r), s) | (M r, s) <- kvs ]
          sets  = [ s | (IL.PAbs _ s, _) <- absProcs ]
          procs = concProcs ++ absProcs

emptyState :: SymbState
emptyState = SymbState { renv = M.empty
                       , renvs = []
                       , ctr = 1
                       , ntypes = 0
                       , me = S (RS 0)
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
freshVar = V <$> freshInt

newtype SymbEx a = SE { runSE :: SymbExM (AbsVal a) }

data AbsVal t where
  AUnit      :: Maybe (Var t) -> AbsVal ()
  AInt       :: Maybe (Var t) -> AbsVal Int
  AString    :: Maybe (Var t) -> AbsVal String
  ASum       :: Maybe (Var t) -> Maybe (AbsVal a) -> Maybe (AbsVal b) -> AbsVal (a :+: b)
  APair      :: Maybe (Var t) -> AbsVal a -> AbsVal b -> AbsVal (a, b)
  AArrow     :: Maybe (Var t) -> (AbsVal a -> SymbEx b) -> AbsVal (a -> b)
  -- "Process" related(
  APid       :: Maybe (Var t) -> L.Pid (Maybe RSing) -> AbsVal (Pid RSing)
  APidMulti  :: Maybe (Var t) -> L.Pid (Maybe RMulti) -> AbsVal (Pid RMulti)
  ARoleSing  :: Maybe (Var t) -> RSing -> AbsVal RSing
  ARoleMulti :: Maybe (Var t) -> RMulti -> AbsVal RMulti
  AProc      :: Maybe (Var t) -> IL.Stmt () -> AbsVal a -> AbsVal (Process SymbEx a)

absToILType :: Typeable t => AbsVal t -> IL.MType
absToILType x = M.fromList $ zip [0..] $ go (typeRep x)
  where
    go :: TypeRep -> [IL.MConstr]
    go a
      | tyConName (typeRepTyCon a) == "()"
        = [IL.MTApp (IL.MTyCon "Unit") []]
      | tyConName (typeRepTyCon a) == "Pid" &&
        "RSing" == (tyConName . typeRepTyCon $ head as)
        = [IL.MTApp (IL.MTyCon "Pid") [IL.PVar (IL.V "x")]]
      | tyConName (typeRepTyCon a) == "[]"
        = [IL.MTApp (IL.MTyCon ("List" ++ concat [ tyConName $ typeRepTyCon a | a <- as ])) []]
      | tyConName (typeRepTyCon a) == "Either"
        =    (IL.MCaseL IL.LL <$> go (as !! 0))
          ++ (IL.MCaseR IL.RL <$> go (as !! 1))
      | tyConName (typeRepTyCon a) == "(,)"
        = [IL.MTProd c1 c2 | c1 <- go (as !! 0), c2 <- go (as !! 1)]
      | otherwise
        = [IL.MTApp (IL.MTyCon (tyConName $ typeRepTyCon a)) []]
      where
        as = typeRepArgs a

-------------------------------------------------
-- | Recv t tells us how to create a default abstraction of type t
-------------------------------------------------
recvTy :: Typeable t => Maybe (Var t) -> AbsVal t
recvTy v = case tyConName $ typeRepTyCon $ typeRep v of
                "Maybe" -> error "LOL"
                _       -> error "OK"

-- instance Recv (Pid RSing) where
--   recvTy v = APid v (Pid Nothing)

-- instance Recv () where
--   recvTy = AUnit

-- instance Recv Int where
--   recvTy = AInt

-- instance Recv String where
--   recvTy = AString

-- instance (Recv a, Recv b) => Recv (a :+: b) where
--   recvTy v = ASum v (Just $ recvTy Nothing) (Just $ recvTy Nothing)

-- instance (Recv a, Recv b) => Recv (a, b) where
--   recvTy v = APair v (recvTy Nothing) (recvTy Nothing)
-------------------------------------------------
-- | An instance of Send t means that t can be sent in a message
-------------------------------------------------
class (Typeable a, Fresh a, AbsValToIL a) => Send a where
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

join :: AbsVal t -> AbsVal t -> AbsVal t          

join (AUnit _) (AUnit _) = AUnit Nothing

join (APid _ (Pid Nothing)) (APid _ _) = APid Nothing (Pid Nothing)
join (APid _ _) (APid _ (Pid Nothing)) = APid Nothing (Pid Nothing)
join (APid _ _) (APid _ _)             = error "Join Pid RSing: TBD"

join (AProc _ s1 a1) (AProc _ s2 a2)
  = AProc Nothing (s1 `joinStmt` s2) (a1 `join` a2)

-------------------------------------------------
-- | Helpers for generating IL from AbsValtractions
-------------------------------------------------
joinStmt :: IL.Stmt () -> IL.Stmt () -> IL.Stmt ()
joinStmt (IL.SSend p1 mts1 _) (IL.SSend p2 mts2 _)
  | p1 == p2 = IL.SSend p1 (mts1 ++ mts2) ()

joinStmt (IL.SRecv mts1 _) (IL.SRecv mts2 _)
  = IL.SRecv (mts1 ++ mts2) ()

joinStmt s1 s2
  | s1 == s2  = s1
  | otherwise = error $ "joinStmt: " ++ show s1 ++ "&" ++ show s2

varToIL :: Var a -> IL.Var
varToIL (V x) = IL.V ("x_" ++ show x)

pidAbsValToIL :: AbsVal (Pid RSing) -> IL.Pid
pidAbsValToIL (APid Nothing (Pid (Just (RS r)))) = IL.PConc r
pidAbsValToIL (APid (Just x) _) = IL.PVar $ varToIL x
pidAbsValToIL _                 = error "pidAbsValToIL: back to the drawing board"

class AbsValToIL a where
  absToIL :: AbsVal a -> [IL.MConstr]

mkVal :: String -> [IL.Pid] -> IL.MConstr
mkVal s = IL.MTApp (IL.MTyCon s)

instance AbsValToIL () where
  absToIL _ = [mkVal "Unit" []]

instance AbsValToIL Int where
  absToIL _ = [mkVal "Int" []]

instance AbsValToIL String where
  absToIL _ = [mkVal "String" []]

instance AbsValToIL (Pid RSing) where
  absToIL (APid Nothing (Pid (Just (RS r)))) = [mkVal "Pid" [IL.PConc r]]
  absToIL (APid (Just x) _)                  = [mkVal "Pid" [IL.PVar $ varToIL x]]
  absToIL _                 = error "absToIL: back to the drawing board"

instance (AbsValToIL a, AbsValToIL b) => AbsValToIL (a :+: b) where
  absToIL (ASum _ (Just a) Nothing)  = IL.MCaseL IL.LL <$> absToIL a
  absToIL (ASum _ Nothing (Just b))  = IL.MCaseR IL.RL <$> absToIL b
  absToIL (ASum (Just x) (Just a) (Just b)) = (IL.MCaseL (IL.VL (varToIL x)) <$> absToIL a)
                                           ++ (IL.MCaseR (IL.VL (varToIL x)) <$> absToIL b)
  absToIL (ASum _ Nothing Nothing)   = error "absToIL sum"

instance (AbsValToIL a, AbsValToIL b) => AbsValToIL (a, b) where
  absToIL (APair _ a b) = do x <- absToIL a
                             y <- absToIL b
                             return $ IL.MTProd x y

-------------------------------------------------
-- | Generate IL from primitive Processes
-------------------------------------------------
sendToIL :: (Serialize SymbEx a) => AbsVal (Pid RSing) -> AbsVal a -> SymbExM (IL.Stmt ())
sendToIL p m = do
  g <- gets tyenv 
  (t, cs) <- unPut $ put (SE $ return m)
  case IL.lookupType g t of
    Just i  -> return $ IL.SSend (pidAbsValToIL p) (mts i g cs) ()
    Nothing -> do i <- freshTId
                  let g' = M.insert i t g
                  modify $ \s -> s { tyenv = g' }
                  return $ IL.SSend (pidAbsValToIL p) (mts i g' cs) ()
  where
    mts i g cs = [ (i, fromMaybe (error (show c)) $ IL.lookupConstr (g M.! i) c, c, skip) | c <- cs ]

recvToIL :: (Serialize SymbEx a) => AbsVal a -> SymbExM (IL.Stmt ())
recvToIL m = do
  g <- gets tyenv 
  (t, cs) <- unPut $ put (SE $ return m)
  case IL.lookupType g t of
    Just i  -> return $ IL.SRecv (mts i g cs) ()
    Nothing -> do i <- freshTId
                  let g' = M.insert i t g
                  modify $ \s -> s { tyenv = g' }
                  return $ IL.SRecv (mts i g' cs) ()
  where
    mts i g cs = [ (i, fromMaybe (error (show c)) $ IL.lookupConstr (g M.! i) c, c, skip) | c <- cs ]

skip :: IL.Stmt ()
skip = IL.SSkip ()

-------------------------------------------------
-- | Sequence Statements
-------------------------------------------------
seqStmt :: IL.Stmt () -> IL.Stmt () -> IL.Stmt ()

seqStmt (IL.SSend p mts ()) s
  = IL.SSend p (map (\(i, c, t, s') -> (i, c, t, seqStmt s' s)) mts) ()

seqStmt (IL.SRecv mts ()) s
  = IL.SRecv (map (\(i, c, t, s') -> (i, c, t, seqStmt s' s)) mts) ()

seqStmt (IL.SSkip _) s = s
seqStmt s (IL.SSkip _) = s

seqStmt (IL.SBlock ss _) (IL.SBlock ss' _) = IL.SBlock (ss ++ ss') ()

seqStmt s (IL.SBlock ss _) = IL.SBlock (s : ss) ()
seqStmt (IL.SBlock ss _) s = IL.SBlock (ss ++ [s]) ()

seqStmt s1 s2 = IL.SBlock [s1, s2] ()

-------------------------------------------------
-- | Updates to roles
-------------------------------------------------
insRoleM :: Role -> SymbEx (Process SymbEx a) -> SymbExM ()
insRoleM k p = do m <- gets renv
                  case M.lookup k m of
                    Nothing -> do
                      AProc _ st _ <- runSE p
                      modify $ \s -> s { renv = M.insert k st (renv s) }
                    Just _  ->
                      error $ "insRoleM attempting to spawn already spawned role" ++ show k

symSpawnSingle :: SymbEx RSing -> SymbEx (Process SymbEx a) -> SymbEx (Process SymbEx (Pid RSing))
symSpawnSingle r p = SE $ do (ARoleSing _ r') <- runSE r
                             insRoleM (S r') p
                             return $ AProc Nothing skip (APid Nothing (Pid (Just r')))

symSpawnMany :: SymbEx RMulti -> SymbEx Int -> SymbEx (Process SymbEx a) -> SymbEx (Process SymbEx (Pid RMulti))
symSpawnMany r _ p = SE $ do (ARoleMulti _ r') <- runSE r
                             insRoleM (M r') p
                             return $ AProc Nothing skip (APidMulti Nothing (Pid (Just r')))

-------------------------------------------------
-- | The Syntax-directed Symbolic Execution
-------------------------------------------------

-------------------------------------------------
symtt :: SymbEx ()
-------------------------------------------------
symtt
  = SE . return $ AUnit Nothing

-------------------------------------------------
symInt :: Int -> SymbEx Int
-------------------------------------------------
symInt _
  = SE . return $ AInt Nothing

-------------------------------------------------
symStr :: String -> SymbEx String
-------------------------------------------------
symStr _
  = SE . return $ AString Nothing

-------------------------------------------------
symLam :: (SymbEx a -> SymbEx b) -> SymbEx (a -> b)
-------------------------------------------------
symLam f
  = SE . return $ AArrow Nothing $ \a -> f (SE $ return a)

-------------------------------------------------
symApp :: SymbEx (a -> b) -> SymbEx a -> SymbEx b
-------------------------------------------------
symApp e1 e2
  = SE $ do AArrow _ f' <- runSE e1
            e2'         <- runSE e2
            runSE (f' e2')

-------------------------------------------------
symSelf :: SymbEx (Process SymbEx (Pid RSing))
-------------------------------------------------
symSelf
  = SE $ do S r <- gets me
            return . AProc Nothing skip $ APid Nothing (Pid (Just r))

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
symFixM :: SymbEx ((a -> Process SymbEx a) -> a -> Process SymbEx a) -> SymbEx (a -> Process SymbEx a)
-------------------------------------------------
symFixM f
  = SE $ do n <- freshInt
            let v = IL.LV $ "L" ++ show n
                sv = IL.SVar v  ()
                g = SE . return . AArrow Nothing $
                       \a -> SE $ return (AProc Nothing sv a)
            return $ AArrow Nothing $ \a -> SE $ do AArrow _ h <- runSE (app f g)
                                                    AProc b s r <- runSE (h a)
                                                    return $ AProc b (IL.SLoop v s ()) r
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
symDoMany :: SymbEx (Pid RMulti)
          -> SymbEx (Pid RSing -> Process SymbEx a)
          -> SymbEx (Process SymbEx ())
-------------------------------------------------
symDoMany p f
  = SE $ do v <- freshVar
            APidMulti _ (Pid (Just r)) <- runSE p
            AArrow _ g                 <- runSE f
            AProc _ s _                <- runSE (g (APid (Just v) (Pid Nothing)))
            return (AProc Nothing (iter v r s) (AUnit Nothing))
    where
      iter v r s = IL.SIter (varToIL v) (roleToSet r) s ()

roleToSet :: RMulti -> IL.Set
roleToSet (RM n) = IL.S $ "role_" ++ show n
-------------------------------------------------
symExec :: SymbEx (Process SymbEx a)
        -> SymbEx a
-------------------------------------------------
symExec p
  = SE $ do (AProc _ st a) <- runSE p
            modify $ \s -> s { renv  = M.empty
                             , renvs = M.insert (me s) st (renv s) : renvs s
                             }
            return a

-------------------------------------------------
symRecv :: (Serialize SymbEx a)
        => SymbEx (Process SymbEx a)
-------------------------------------------------
symRecv
  = SE $ do v     <- unGet get
            s     <- recvToIL v
            return $ AProc Nothing s v

-- recv(x : A + (B * C))
-- ASum (Just x) (Just (... y ) (Just ...))

class Fresh a where
  freshVal :: SymbExM (AbsVal a)

instance Fresh () where
  freshVal = (AUnit . Just) <$> freshVar

instance Fresh Int where
  freshVal = (AInt . Just) <$> freshVar

instance Fresh String where
  freshVal = (AString . Just) <$> freshVar

instance Fresh (Pid RSing) where
  freshVal = do b <- freshVar
                return $ APid (Just b) (Pid Nothing)

instance (Fresh a, Fresh b) => Fresh (a :+: b) where
  freshVal = do x <- Just <$> freshVal
                y <- Just <$> freshVal
                b <- Just <$> freshVar
                return $ ASum b x y

instance (Fresh a, Fresh b) => Fresh (a,b) where
  freshVal = do x <- freshVal
                y <- freshVal
                b <- Just <$> freshVar
                return $ APair b x y

-------------------------------------------------
symSend :: (Serialize SymbEx a)
        => SymbEx (Pid RSing)
        -> SymbEx a
        -> SymbEx (Process SymbEx ())
-------------------------------------------------
symSend pidM mM
  = SE $ do p <- runSE pidM
            m <- runSE mM
            s <- sendToIL p m
            return (AProc Nothing s (AUnit Nothing))

symInL :: SymbEx a
       -> SymbEx (a :+: b)
symInL a = SE $ do av <- runSE a
                   return $ ASum Nothing (Just av) Nothing
symInR :: SymbEx b
       -> SymbEx (a :+: b)
symInR b = SE $ do bv <- runSE b
                   return $ ASum Nothing Nothing (Just bv)

symMatch :: forall a b c.
            (Typeable a, Typeable b) =>
            SymbEx (a :+: b)
         -> SymbEx (a -> c)
         -> SymbEx (b -> c)
         -> SymbEx c
symMatch s l r
  = SE $ do ASum x vl vr <- runSE s
            case (vl, vr) of
              (Just a, Nothing) -> runSE . app l . SE $ return a
              (Nothing, Just b) -> runSE . app r . SE $ return b
              (Nothing, Nothing) -> do
                (v1, v2) <- case x of
                              Nothing -> error "does this happen?" -- return (Nothing, Nothing)
                              _       -> do v1 <- freshVar
                                            v2 <- freshVar
                                            return (Just v1, Just v2)
                let (val1, val2) = (recvTy v1, recvTy v2)
                c1 <- runSE . app l . SE . return $ val1
                c2 <- runSE . app r . SE . return $ val2
                return $ join c1 c2
              (Just a, Just b)  -> do 
                c1 <- runSE . app l . SE . return $ a
                c2 <- runSE . app r . SE . return $ b
                return $ join c1 c2

symMatchProc :: forall a b c. 
            (Typeable a, Typeable b)
         => SymbEx (a :+: b)
         -> SymbEx (a -> Process SymbEx c)
         -> SymbEx (b -> Process SymbEx c)
         -> SymbEx (Process SymbEx c)
symMatchProc s l r
  = SE $ do ASum x vl vr <- runSE s
            case (vl, vr) of
              (Just a, Nothing) -> runSE . app l . SE $ return a
              (Nothing, Just b) -> runSE . app r . SE $ return b
              (Just a, Just b)  ->
                case x of
                  Nothing -> do
                    AProc _ _ v1 <- runSE . app l . SE . return $ (recvTy Nothing :: AbsVal a)
                    AProc _ _ v2 <- runSE . app r . SE . return $ (recvTy Nothing :: AbsVal b)
                    return $ AProc Nothing (error "TBD: symMatchProc") (v1 `join` v2)
                  Just y  -> do
                    px <- freshVar
                    py <- freshVar
                    AProc _ s1 v1 <- runSE . app l . SE . return $ a
                    AProc _ s2 v2 <- runSE . app r . SE . return $ b
                    return $ AProc Nothing (IL.SCase (varToIL y) s1 s2 ()) (v1 `join` v2)


                         -- return $ AProc Nothing (IL.SSkip ()) (recvTy Nothing)
                -- (val1, val2) <- case x of
                --               Nothing -> return (recvTy Nothing, recvTy Nothing)
                --               _       -> do v1 <- freshVar
                --                             v2 <- freshVar
                --                             return (recvTy $ Just v1, recvTy $ Just v2)
                -- AProc _ s1 c1 <- runSE . app l . SE . return $ val1
                -- AProc _ s2 c2 <- runSE . app r . SE . return $ val2
                -- return $ AProc Nothing s1 (c1 `join` c2)

symPair :: SymbEx a
        -> SymbEx b
        -> SymbEx (a, b)
symPair a b
  = SE $ do av <- runSE a
            bv <- runSE b
            return $ APair Nothing av bv

symProj1 :: SymbEx (a, b)
         -> SymbEx a
symProj1 p = SE $ do p' <- runSE p
                     case p' of
                       APair _ a _ -> return a

symProj2 :: SymbEx (a, b)
         -> SymbEx b
symProj2 p = SE $ do p' <- runSE p
                     case p' of
                       APair _ _ b -> return b

-------------------------------------------------
-- Instances
-------------------------------------------------
instance Symantics SymbEx where
  data Process SymbEx a = P a
  tt        = symtt
  int       = symInt
  str       = symStr
  bool      = error "TBD: bool"
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
  die       = error "TBD: die"

  inl   = symInL
  inr   = symInR
  pair  = symPair
  proj1 = symProj1
  proj2 = symProj2

  recv = symRecv
  send = symSend

-- newtype Id x = I x

-- instance (Recv a, AbsValToIL a) => SymPat SymbEx Id a where
--   pat = I . SE . return $ recvTy Nothing

-- instance {-# OVERLAPPABLE #-}(SymPat SymbEx Id a, SymPat SymbEx Id b, Join c, Pure c) => SymMatch SymbEx Id a b c where
-- -- instance {-# OVERLAPPABLE #-}(Recv a, Recv b, AbsValToIL a, AbsValToIL b, Join c, Pure c) => SymMatch SymbEx a b c where
--   match = symMatch

-- instance {-# OVERLAPPING #-} (SymPat SymbEx Id a, SymPat SymbEx Id b, Join c, Pure c) => SymMatch SymbEx Id a b (Process SymbEx c) where
--   match = symMatchProc
instance SymMatch SymbEx where
  match = symMatch


-- if_ :: (SymMatch repr pat a b c, Symantics repr)
--     => repr (a :+: b) -> repr (a -> c) -> repr (b -> c) -> repr c
-- if_ = match
--
instance (Fresh a, Typeable a, AbsValToIL a) => Serialize SymbEx a where
  data Put SymbEx   = Put { unPut :: SymbExM (IL.MType, [IL.MConstr]) }
  data Get SymbEx a = Get { unGet :: SymbExM (AbsVal a)  }
  put x = Put $ do v <- runSE x
                   return (absToILType v, absToIL v)
  get = Get freshVal
