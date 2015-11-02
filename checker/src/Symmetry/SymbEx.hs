{-# Language TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, GADTs #-}
{-# Language FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing  #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language ScopedTypeVariables #-}
module Symmetry.SymbEx where

import           Data.Generics
import           Data.Maybe

import qualified Data.Map.Strict as M
import           Control.Monad.State hiding (join, get, put)
import           Symmetry.Language.AST as L
import qualified Symmetry.IL.AST       as IL

data Var a = V Int deriving (Ord, Eq, Show)

type REnv = M.Map Role (IL.Stmt ())

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
                            , IL.cSets  = []
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

fresh :: AbsVal t -> SymbExM (AbsVal t)
fresh (AUnit _)    = AUnit . Just <$> freshVar
fresh (AInt _)     = AInt . Just <$> freshVar
fresh (AString _)  = AString . Just <$> freshVar
fresh (ASum _ l r) = do v  <- Just <$> freshVar
                        fl <- mapM fresh l
                        fr <- mapM fresh r
                        return $ ASum v fl fr
fresh (AProd _ l r) = do v  <- Just <$> freshVar
                         fl <- fresh l
                         fr <- fresh r
                         return $ AProd v fl fr
fresh (AList _ l)   = AList <$> (Just <$> freshVar) <*> mapM fresh l 
fresh (AArrow _ f)  = do v <- Just <$> freshVar 
                         return $ AArrow v f
fresh (APid _ p) = do v <- Just <$> freshVar
                      return $ APid v p
fresh (APidMulti _ p) = do v <- Just <$> freshVar
                           return $ APidMulti v p
fresh (ARoleSing _ p) = do v <- Just <$> freshVar
                           return $ ARoleSing v p
fresh (ARoleMulti _ p) = do v <- Just <$> freshVar
                            return $ ARoleMulti v p
fresh (AProc _ s a) = do v <- Just <$> freshVar
                         return $ AProc v s a

newtype SymbEx a = SE { runSE :: SymbExM (AbsVal a) }

data AbsVal t where
  ABot        :: AbsVal t
  APidCompare :: (Maybe (Var (Pid RSing)), L.Pid (Maybe RSing))
              -> (Maybe (Var (Pid RSing)), L.Pid (Maybe RSing))
              -> AbsVal Boolean
  --
  AUnit      :: Maybe (Var ()) -> AbsVal ()
  AInt       :: Maybe (Var Int) -> AbsVal Int
  AString    :: Maybe (Var String) -> AbsVal String
  ASum       :: Maybe (Var (a :+: b)) -> Maybe (AbsVal a) -> Maybe (AbsVal b) -> AbsVal (a :+: b)
  AProd      :: Maybe (Var (a,b)) -> AbsVal a -> AbsVal b -> AbsVal (a, b)
  AList      :: Maybe (Var [a]) -> Maybe (AbsVal a) -> AbsVal [a]
  AArrow     :: Maybe (Var (a -> b)) -> (AbsVal a -> SymbEx b) -> AbsVal (a -> b)
  APid       :: Maybe (Var (Pid RSing)) -> L.Pid (Maybe RSing) -> AbsVal (Pid RSing)
  APidMulti  :: Maybe (Var (Pid RMulti)) -> L.Pid (Maybe RMulti) -> AbsVal (Pid RMulti)
  ARoleSing  :: Maybe (Var RSing) -> RSing -> AbsVal RSing
  ARoleMulti :: Maybe (Var RMulti) -> RMulti -> AbsVal RMulti
  AProc      :: Maybe (Var (Process SymbEx a)) -> IL.Stmt () -> AbsVal a -> AbsVal (Process SymbEx a)

instance Show (AbsVal t) where
  show (AUnit _) = "AUnit"
  show (AInt _) = "AInt"
  show (AString _) = "AString"
  show (ASum _ l r) = show l ++ "+" ++ show r
  show (AProd _ l r) = show l ++ "*" ++ show r
  show (APid x p) = show p ++ "@" ++ show x 

setVar :: Var t -> AbsVal t -> AbsVal t                
setVar v (AUnit _)       = AUnit (Just v)
setVar v (ASum _ l r)    = ASum  (Just v) l r
setVar v (APid _ p)      = APid  (Just v) p
setVar v (AProd _ p1 p2) = AProd (Just v) p1 p2

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
      | tyConName (typeRepTyCon a) == "[]" &&
        tyConName (typeRepTyCon $ head as) == "Char"
        = [IL.MTApp (IL.MTyCon "String") []]
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
  arb = SE . return $ AInt Nothing

instance {-# OVERLAPPING #-} ArbPat SymbEx String where            
  arb = SE . return $ AString Nothing

instance ArbPat SymbEx (Pid RSing) where            
  arb = SE . return $ APid Nothing (Pid Nothing)

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

join :: AbsVal t -> AbsVal t -> AbsVal t          

join ABot x = x
join x    ABot = x

join (AUnit _) (AUnit _) = AUnit Nothing
join (AInt _)  (AInt _)  = AInt Nothing

join (APid _ (Pid Nothing)) (APid _ _) = APid Nothing (Pid Nothing)
join (APid _ _) (APid _ (Pid Nothing)) = APid Nothing (Pid Nothing)
join (APid _ _) (APid _ _)             = error "Join Pid RSing: TBD"

join (AProc _ s1 a1) (AProc _ s2 a2)
  = AProc Nothing (s1 `joinStmt` s2) (a1 `join` a2)

join (ASum _ l1 r1) (ASum _ l2 r2)
  = ASum Nothing (l1 `maybeJoin` l2) (r1 `maybeJoin` r2)
  where
    maybeJoin :: forall a. Maybe (AbsVal a) -> Maybe (AbsVal a) -> Maybe (AbsVal a)
    maybeJoin (Just x) (Just y) = Just (x `join` y)
    maybeJoin (Just x) Nothing  = Just x
    maybeJoin _  y              = y

join (AProd _ l1 r1) (AProd _ l2 r2)
  = AProd Nothing l1 r1

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
-- Oy
pidAbsValToIL (APid Nothing (Pid (Just (RSelf (S (RS r)))))) = IL.PConc r
pidAbsValToIL _                 = error "pidAbsValToIL: back to the drawing board "


mkVal :: String -> [IL.Pid] -> IL.MConstr
mkVal s = IL.MTApp (IL.MTyCon s)

absToIL :: AbsVal a -> [IL.MConstr]
absToIL (AUnit _) = [mkVal "Unit" []]
absToIL (AInt  _) = [mkVal "Int" []]
absToIL (AString _) = [mkVal "String" []]

absToIL (APid Nothing (Pid (Just (RS r))))    = [mkVal "Pid" [IL.PConc r]]
absToIL (APid Nothing (Pid (Just (RSelf (S (RS r)))))) = [mkVal "Pid" [IL.PConc r]]
absToIL (APid Nothing (Pid (Just (RSelf (M r))))) = [mkVal "Pid" [IL.PAbs (IL.V "i") (roleToSet r)]]
absToIL (APid (Just x) _)                     = [mkVal "Pid" [IL.PVar $ varToIL x]]
absToIL (APid Nothing (Pid Nothing))          = error "wut"

absToIL (ASum _ (Just a) Nothing)  = IL.MCaseL IL.LL <$> absToIL a
absToIL (ASum _ Nothing (Just b))  = IL.MCaseR IL.RL <$> absToIL b
absToIL (ASum (Just x) (Just a) (Just b)) = (IL.MCaseL (IL.VL (varToIL x)) <$> absToIL a)
                                         ++ (IL.MCaseR (IL.VL (varToIL x)) <$> absToIL b)
absToIL (ASum _ Nothing Nothing)   = error "absToIL sum"

absToIL (AProd _ a b) = do x <- absToIL a
                           y <- absToIL b
                           return $ IL.MTProd x y

-------------------------------------------------
-- | Generate IL from primitive Processes
-------------------------------------------------
sendToIL :: (Typeable a) => AbsVal (Pid RSing) -> AbsVal a -> SymbExM (IL.Stmt ())
sendToIL p m = do
  g <- gets tyenv 
  let t  = absToILType m
  let cs = absToIL m
  -- (t, cs) <- unPut $ put (SE $ return m)
  case IL.lookupType g t of
    Just i  -> return $ IL.SSend (pidAbsValToIL p) [(i, mts i g cs, skip)] ()
    Nothing -> do i <- freshTId
                  let g' = M.insert i t g
                  modify $ \s -> s { tyenv = g' }
                  return $ IL.SSend (pidAbsValToIL p) [(i, mts i g' cs, skip)] ()
  where
    mts i g cs = [ (fromMaybe (error ("send:" ++ show c)) $ IL.lookupConstr (g M.! i) c, c) | c <- cs ]

recvToIL :: (Typeable a) => AbsVal a -> SymbExM (IL.Stmt ())
recvToIL m = do
  g <- gets tyenv 
  let t  = absToILType m
  let cs = absToIL m
  case IL.lookupType g t of
    Just i  -> return $ IL.SRecv [(i, mts i g cs, skip)] ()
    Nothing -> do i <- freshTId
                  let g' = M.insert i t g
                  modify $ \s -> s { tyenv = g' }
                  return $ IL.SRecv [(i, mts i g' cs, skip)] ()
  where
    mts i g cs = [ (fromMaybe (error ("recv:" ++ show c)) $ IL.lookupConstr (g M.! i) c, c) | c <- cs ]

skip :: IL.Stmt ()
skip = IL.SSkip ()

-------------------------------------------------
-- | Sequence Statements
-------------------------------------------------
seqStmt :: IL.Stmt () -> IL.Stmt () -> IL.Stmt ()

seqStmt (IL.SSend p mts ()) s
  = IL.SSend p (map (\(i, cs, s') -> (i, cs, seqStmt s' s)) mts) ()

seqStmt (IL.SRecv mts ()) s
  = IL.SRecv (map (\(i, cs, s') -> (i, cs, seqStmt s' s)) mts) ()

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
                      oldMe <- gets me
                      modify $ \s -> s { me = k }
                      AProc _ st _ <- runSE p
                      modify $ \s -> s { renv = M.insert k st (renv s), me = oldMe }
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
symEq, symGt, symLt :: Ord a
                    => SymbEx a
                    -> SymbEx a
                    -> SymbEx Boolean
-------------------------------------------------
symEq a b  = SE $ do av <- runSE a
                     bv <- runSE b
                     case (av, bv) of
                       (APid ax apid, APid bx bpid) ->
                         return $ APidCompare (ax, apid) (bx, bpid)
                       _ ->
                         runSE arb
                       
symGt _ _  = arb
symLt _ _  = arb

-------------------------------------------------
symNot :: SymbEx Boolean -> SymbEx Boolean
-------------------------------------------------
symNot _   = arb

-------------------------------------------------
symAnd, symOr :: SymbEx Boolean
              -> SymbEx Boolean
              -> SymbEx Boolean
-------------------------------------------------
symAnd _ _ = arb
symOr  _ _ = arb

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
                SymbEx [a]
             -> SymbEx (() -> b)
             -> SymbEx ((a, [a]) -> b)
             -> SymbEx b         
symMatchList l nilCase consCase
  = SE $ do nilv  <- runSE (app nilCase tt)
            lv    <- runSE l
            case lv of
              AList _ (Just v) -> do
                      let tl = SE . return $ AList Nothing Nothing
                      cv <- runSE $ symApp consCase (pair (SE . return $ v) tl)
                      return (cv `join` nilv)
              AList _ Nothing  -> return nilv

-------------------------------------------------
symSelf :: SymbEx (Process SymbEx (Pid RSing))
-------------------------------------------------
symSelf
  = SE $ do r <- gets me
            let role = RSelf r
            return . AProc Nothing skip $ APid Nothing (Pid (Just role))

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
  = SE . return . AArrow Nothing $ \a ->
          SE $ do n <- freshInt
                  let v = IL.LV $ "L" ++ show n
                      sv = IL.SVar v  ()
                      g = SE . return . AArrow Nothing $ \a -> SE $ return (AProc Nothing sv a)
                  AArrow _ h <- runSE (app f g)
                  AProc b s r <- prohibitSpawn $ runSE (h a)
                  return $ AProc b (IL.SLoop v s ()) r
  where
    prohibitSpawn m
      = do env <- gets renv
           r    <- m
           env' <- gets renv
           when (env /= env') err
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
symDoMany :: SymbEx (Pid RMulti)
          -> SymbEx (Pid RSing -> Process SymbEx a)
          -> SymbEx (Process SymbEx [a])
-------------------------------------------------
symDoMany p f
  = SE $ do v <- freshVar
            APidMulti _ (Pid (Just r)) <- runSE p
            AArrow _ g                 <- runSE f
            AProc _ s _                <- runSE (g (APid (Just v) (Pid Nothing)))
            return (AProc Nothing (iter v r s) (error "TBD: symDoMany"))
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
symRecv :: (Typeable a, ArbPat SymbEx a)
        => SymbEx (Process SymbEx a)
-------------------------------------------------
symRecv
  = SE $ do v     <- freshVal
            s     <- recvToIL v
            return $ AProc Nothing s v

freshVal :: ArbPat SymbEx a => SymbExM (AbsVal a)
freshVal = runSE arb >>= fresh

-------------------------------------------------
symSend :: Typeable a
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
      s = IL.SDie ()

symInL :: SymbEx a
       -> SymbEx (a :+: b)
symInL a = SE $ do av <- runSE a
                   return $ ASum Nothing (Just av) Nothing
symInR :: SymbEx b
       -> SymbEx (a :+: b)
symInR b = SE $ do bv <- runSE b
                   return $ ASum Nothing Nothing (Just bv)

symMatch :: forall a b c.
            (Typeable a, Typeable b, ArbPat SymbEx a, ArbPat SymbEx b) =>
            SymbEx (a :+: b)
         -> SymbEx (a -> c)
         -> SymbEx (b -> c)
         -> SymbEx c
symMatch s l r
  = SE $ do sum <- runSE s
            case sum of
              s@(APidCompare _ _) -> symMatchCompare s l r
              _                   -> symMatchSum sum l r

symMatchCompare :: forall a b c.
                   (Typeable a, Typeable b, ArbPat SymbEx a, ArbPat SymbEx b) =>
                   AbsVal (a :+: b)
                -> SymbEx (a -> c)
                -> SymbEx (b -> c)
                -> SymbExM (AbsVal c)
symMatchCompare (APidCompare (x,p) (y,q)) l r 
  = do v <- freshVar
       m <- symMatchSum (ASum (Just v) Nothing Nothing) l r
       case m of
         AProc px s a -> do
           let p1 = pidAbsValToIL $ APid x p
           let p2 = pidAbsValToIL $ APid y q
           return $ AProc px (IL.SCompare (varToIL v) p1 p2 () `seqStmt` s) a
         _ -> error "TBD: matchcompare"

symMatchSum :: forall a b c.
               (Typeable a, Typeable b, ArbPat SymbEx a, ArbPat SymbEx b) =>
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
                      _       -> do v1 <- freshVar
                                    v2 <- freshVar
                                    return (v1, v2)
        val1 <- setVar v1 <$> runSE arb
        val2 <- setVar v2 <$> runSE arb
        c1 <- runSE . app l . SE . return $ val1
        c2 <- runSE . app r . SE . return $ val2
        return $ joinProcs x c1 c2
      (Just a, Just b)  -> do 
        c1 <- runSE . app l . SE . return $ a
        c2 <- runSE . app r . SE . return $ b
        case x of
          Nothing -> 
            return $ joinProcs Nothing c1 c2
          Just v -> 
            return $ joinProcs (Just v) c1 c2

joinProcs :: forall a b. Maybe (Var b) -> AbsVal a -> AbsVal a -> AbsVal a
joinProcs (Just x) (AProc _ s1 v1) (AProc _ s2 v2)
  = AProc Nothing (IL.SCase (varToIL x) s1 s2 ()) (v1 `join` v2)
joinProcs _ t1 t2
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
                       AProd _ a _ -> return a

symProj2 :: SymbEx (a, b)
         -> SymbEx b
symProj2 p = SE $ do p' <- runSE p
                     case p' of
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
  matchList = symMatchList

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
  die       = symDie

  inl   = symInL
  inr   = symInR
  pair  = symPair
  proj1 = symProj1
  proj2 = symProj2

  recv = symRecv
  send = symSend

  match = symMatch
