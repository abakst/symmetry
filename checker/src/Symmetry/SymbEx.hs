{-# Language TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, GADTs #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing  #-}
{-# Language TypeOperators #-}
module Symmetry.SymbEx where

import           Data.List (nub)
import           Data.Generics

import           Data.Hashable
import qualified Data.HashMap.Strict as M
import           Control.Monad.State
import           Symmetry.Language.AST as L
import qualified Symmetry.IL.AST       as IL

data Var   = V Int deriving Show

type REnv = M.HashMap Role (IL.Stmt ())
data Role = S RSing
          | M RMulti
            deriving (Eq, Show)

instance Hashable Role where
  hashWithSalt s (S r) = hashWithSalt s r
  hashWithSalt s (M r) = hashWithSalt s r

data SymbState = SymbState { renv  :: REnv
                           , ctr   :: Int
                           , me    :: Role
                           , renvs :: [REnv]
                           }
type SymbExM a = State SymbState a

rEnvToConfig :: REnv -> IL.Config ()
rEnvToConfig renv
  = IL.Config { IL.cTypes = types
              , IL.cSets  = sets
              , IL.cProcs = procs
              , IL.cUnfold = []
              }
    where
      types = nub [ IL.MTApp tc $ mkVars vs | IL.MTApp tc vs <- ts ]
      ts    = listify (const True) procs
      mkVars vs = map (IL.PVar . IL.V . ("x"++) . show) [1..length vs]
      sets  = [ s | (IL.PAbs _ s, _) <- absProcs ]
      procs = concProcs ++ absProcs
      concProcs = [ (IL.PConc n, s) | (S (RS n), s) <- kvs ]
      absProcs  = [ (IL.PAbs (IL.V "i") (roleToSet r), s) | (M r, s) <- kvs ]
      kvs   = M.toList renv

emptyState :: SymbState
emptyState = SymbState { renv = M.empty
                       , renvs = []
                       , ctr = 1
                       , me = S (RS 0)
                       }

runSymb :: SymbEx a -> SymbState
runSymb e = execState (runSE e) emptyState

freshInt :: SymbExM Int
freshInt = do n <- gets ctr
              modify $ \s -> s { ctr = n + 1 }
              return n

freshVar :: SymbExM Var
freshVar = V <$> freshInt

data SymbEx a = SE { runSE :: SymbExM (Abs a) }

data Abs t where
  TUnit :: Maybe Var -> Abs ()
  TInt :: Maybe Var -> Abs Int
  TPid :: Maybe Var -> L.Pid (Maybe RSing) -> Abs (Pid RSing)
  TPidMulti :: Maybe Var -> L.Pid (Maybe RMulti) -> Abs (Pid RMulti)
  TRoleSing :: Maybe Var -> RSing -> Abs RSing
  TRoleMulti :: Maybe Var -> RMulti -> Abs RMulti
  TString :: Maybe Var -> Abs String
  TArrow :: Maybe Var -> (Abs a -> SymbEx b) -> Abs (a -> b)
  TProc :: Maybe Var -> IL.Stmt () -> Abs a -> Abs (L.Process a)
  TSum  :: Maybe Var -> Abs a :+: Abs b -> Abs (a :+: b)
  TPair :: Maybe Var -> Abs a -> Abs b -> Abs (a, b)

-------------------------------------------------
-- | Recv t tells us how to create a default abstraction of type t
-------------------------------------------------
class Recv t where
  recvTy :: Maybe Var -> Abs t

instance Recv (Pid RSing) where
  recvTy v = TPid v (Pid Nothing)

instance Recv () where
  recvTy = TUnit
-------------------------------------------------
-- | An instance of Send t means that t can be sent in a message
-------------------------------------------------
class Send t where
  -- This line intentionally left blank

instance Send (Pid RSing) where
  -- This line intentionally left blank

instance Send (()) where
  -- This line intentionally left blank

-------------------------------------------------
-- | Helpers for generating IL from Abstractions
-------------------------------------------------
varToIL :: Var -> IL.Var
varToIL (V x) = IL.V ("x" ++ show x)

pidAbsToIL :: Abs (Pid RSing) -> IL.Pid
pidAbsToIL (TPid Nothing (Pid (Just (RS r)))) = IL.PConc r
pidAbsToIL (TPid (Just x) _) = IL.PVar $ varToIL x
pidAbsToIL _                 = error "pidAbsToIL: back to the drawing board"

mkTy :: String -> [IL.Pid] -> IL.MType
mkTy s = IL.MTApp (IL.MTyCon s)

class AbsToIL a where
  absToIL :: Abs a -> IL.MType

instance AbsToIL () where
  absToIL _ = mkTy "tt" []

instance AbsToIL (Pid RSing) where
  absToIL (TPid Nothing (Pid (Just (RS r)))) = mkTy "Pid" [IL.PConc r]
  absToIL (TPid (Just x) _)                  = mkTy "Pid" [IL.PVar $ varToIL x]
  absToIL _                 = error "absToIL: back to the drawing board"

-------------------------------------------------
-- | Generate IL from primitive Processes
-------------------------------------------------

sendToIL :: (AbsToIL a, Send a) => Abs (Pid RSing) -> Abs a -> IL.Stmt ()
sendToIL p m = IL.SSend (pidAbsToIL p) [(absToIL m, IL.SSkip ())] ()

recvToIL :: (AbsToIL a, Recv a) => Abs a -> IL.Stmt ()
recvToIL m = IL.SRecv [(absToIL m, IL.SSkip ())] ()

skip :: IL.Stmt ()
skip = IL.SSkip ()

-------------------------------------------------
-- | Sequence Statements
-------------------------------------------------
seqStmt :: IL.Stmt () -> IL.Stmt () -> IL.Stmt ()

seqStmt (IL.SSend p mts ()) s
  = IL.SSend p (map (\(t, s') -> (t, seqStmt s' s)) mts) ()

seqStmt (IL.SRecv mts ()) s
  = IL.SRecv (map (\(t, s') -> (t, seqStmt s' s)) mts) ()

seqStmt (IL.SSkip _) s = s
seqStmt s (IL.SSkip _) = s

seqStmt s1 s2 = IL.SBlock [s1, s2] ()

-------------------------------------------------
-- | Updates to roles
-------------------------------------------------
insRoleM :: Role -> SymbEx (Process a) -> SymbExM ()
insRoleM k p = do m <- gets renv
                  case M.lookup k m of
                    Nothing -> do
                      TProc _ st _ <- runSE p
                      modify $ \s -> s { renv = M.insert k st (renv s) }
                    Just _  ->
                      error $ "insRoleM attempting to spawn already spawned role" ++ show k

symSpawnSingle :: SymbEx RSing -> SymbEx (Process a) -> SymbEx (Process (Pid RSing))
symSpawnSingle r p = SE $ do (TRoleSing _ r') <- runSE r
                             insRoleM (S r') p
                             return $ TProc Nothing skip (TPid Nothing (Pid (Just r')))

symSpawnMany :: SymbEx RMulti -> SymbEx Int -> SymbEx (Process a) -> SymbEx (Process (Pid RMulti))
symSpawnMany r _ p = SE $ do (TRoleMulti _ r') <- runSE r
                             insRoleM (M r') p
                             return $ TProc Nothing skip (TPidMulti Nothing (Pid (Just r')))

-------------------------------------------------
-- | The Syntax-directed Symbolic Execution
-------------------------------------------------

-------------------------------------------------
symtt :: SymbEx ()
-------------------------------------------------
symtt
  = SE . return $ TUnit Nothing

-------------------------------------------------
symRep :: Int -> SymbEx Int
-------------------------------------------------
symRep _
  = SE . return $ TInt Nothing

-------------------------------------------------
symRepS :: String -> SymbEx String
-------------------------------------------------
symRepS _
  = SE . return $ TString Nothing

-------------------------------------------------
symLam :: (SymbEx a -> SymbEx b) -> SymbEx (a -> b)
-------------------------------------------------
symLam f
  = SE . return $ TArrow Nothing $ \a -> f (SE $ return a)

-------------------------------------------------
symApp :: SymbEx (a -> b) -> SymbEx a -> SymbEx b
-------------------------------------------------
symApp e1 e2
  = SE $ do TArrow _ f' <- runSE e1
            e2'         <- runSE e2
            runSE (f' e2')

-------------------------------------------------
symSelf :: SymbEx (Process (Pid RSing))
-------------------------------------------------
symSelf
  = SE $ do S r <- gets me
            return . TProc Nothing skip $ TPid Nothing (Pid (Just r))

-------------------------------------------------
symRet :: SymbEx a -> SymbEx (Process a)
-------------------------------------------------
symRet x
  = SE $ do a <- runSE x
            return (TProc Nothing skip a)
-------------------------------------------------
symBind :: SymbEx (Process a) -> SymbEx (a -> Process b) -> SymbEx (Process b)
-------------------------------------------------
symBind mm mf
  = SE $ do TProc _ st a  <- runSE mm
            TArrow _ f <- runSE mf
            TProc _ st' b <- runSE $ f a
            return $ TProc Nothing (st `seqStmt` st') b

-------------------------------------------------
symFixM :: SymbEx ((a -> Process a) -> a -> Process a) -> SymbEx (a -> Process a)
-------------------------------------------------
symFixM f
  = SE $ do n <- freshInt
            let v = IL.LV $ "L" ++ show n
                sv = IL.SVar v  ()
                g = SE . return . TArrow Nothing $
                       \a -> SE $ return (TProc Nothing sv a)
            return $ TArrow Nothing $ \a -> SE $ do TArrow _ h <- runSE (app f g)
                                                    TProc b s r <- runSE (h a)
                                                    return $ TProc b (IL.SLoop v s ()) r
-------------------------------------------------
symNewRSing :: SymbEx (Process RSing)
-------------------------------------------------
symNewRSing
  = SE $ do n <- freshInt
            return (TProc Nothing skip (TRoleSing Nothing (RS n)))

-------------------------------------------------
symNewRMulti :: SymbEx (Process RMulti)
-------------------------------------------------
symNewRMulti
  = SE $ do n <- freshInt
            return (TProc Nothing skip (TRoleMulti Nothing (RM n)))

-------------------------------------------------
symDoMany :: SymbEx (Pid RMulti)
          -> SymbEx (Pid RSing -> Process a)
          -> SymbEx (Process ())
-------------------------------------------------
symDoMany p f
  = SE $ do v <- freshVar
            TPidMulti _ (Pid (Just r)) <- runSE p
            TArrow _ g                 <- runSE f
            TProc _ s _                <- runSE (g (TPid (Just v) (Pid Nothing)))
            return (TProc Nothing (iter v r s) (TUnit Nothing))
    where
      iter v r s = IL.SIter (varToIL v) (roleToSet r) s ()

roleToSet :: RMulti -> IL.Set
roleToSet (RM n) = IL.S $ "role_" ++ show n
-------------------------------------------------
symExec :: SymbEx (Process a)
        -> SymbEx a
-------------------------------------------------
symExec p
  = SE $ do (TProc _ st a) <- runSE p
            modify $ \s -> s { renv  = M.empty
                             , renvs = M.insert (me s) st (renv s) : renvs s
                             }
            return a

-------------------------------------------------
symRecv :: (Recv a, AbsToIL a)
        => SymbEx (Process a)
-------------------------------------------------
symRecv
  = SE $ do x <- freshVar
            let tr = recvTy (Just x)
            return $ TProc Nothing (recvToIL tr) tr
-------------------------------------------------
symSend :: (Send a, AbsToIL a)
        => SymbEx (Pid RSing)
        -> SymbEx a
        -> SymbEx (Process ())
-------------------------------------------------
symSend pidM mM
  = SE $ do p <- runSE pidM
            m <- runSE mM
            return (TProc Nothing (sendToIL p m) (TUnit Nothing))

symInL :: SymbEx a
       -> SymbEx (a :+: b)
symInL a = SE $ do av <- runSE a
                   return $ TSum Nothing (Left av)
symInR :: SymbEx b
       -> SymbEx (a :+: b)
symInR b = SE $ do bv <- runSE b
                   return $ TSum Nothing (Right bv)

symMatch :: SymbEx (a :+: b)
         -> SymbEx (a -> c)
         -> SymbEx (b -> c)
         -> SymbEx c
symMatch s l r
  = SE $ do TSum _ v <- runSE s
            case v of
              Left a -> runSE . app l . SE $ return a
              Right b -> runSE . app r . SE $ return b

symPair :: SymbEx a
        -> SymbEx b
        -> SymbEx (a, b)
symPair a b
  = SE $ do av <- runSE a
            bv <- runSE b
            return $ TPair Nothing av bv

symProj1 :: SymbEx (a, b)
         -> SymbEx a
symProj1 p = SE $ do TPair _ a _ <- runSE p
                     return a

symProj2 :: SymbEx (a, b)
         -> SymbEx b
symProj2 p = SE $ do TPair _ _ b <- runSE p
                     return b

-------------------------------------------------
-- Instances
-------------------------------------------------
instance Symantics SymbEx where
  tt        = symtt
  repI      = symRep
  repS      = symRepS
  inl       = symInL
  inr       = symInR
  pair      = symPair
  proj1     = symProj1
  proj2     = symProj2
  match     = symMatch
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

instance (Recv a, AbsToIL a) => SymRecv SymbEx a where
  recv = symRecv

instance (Send a, AbsToIL a) => SymSend SymbEx a where
  send = symSend
