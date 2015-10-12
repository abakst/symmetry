{-# Language TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, GADTs #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing  #-}
module SymbEx where

import           Data.Hashable
import qualified Data.HashMap.Strict as M
import           Control.Monad.State
import           Language.AST as L
import qualified AST          as IL

data Var   = V Int deriving Show

-- type Env  = M.HashMap Var AbsVal
type REnv = M.HashMap Role (Maybe (IL.Stmt ()))
data Role = S RSing
          | M RMulti
            deriving (Eq, Show)

instance Hashable Role where
  hashWithSalt s (S r) = hashWithSalt s r
  hashWithSalt s (M r) = hashWithSalt s r

data SymbState = SymbState { renv :: REnv
                           , ctr  :: Int
                           , me   :: Role
                           }
type SymbExM a = State SymbState a

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
symSpawnSingle :: SymbEx RSing -> SymbEx (Process a) -> SymbEx (Process (Pid RSing))
symSpawnSingle r p = SE $ do (TRoleSing _ r') <- runSE r
                             m <- gets renv
                             case M.lookup (S r') m of
                               Just Nothing -> do
                                 TProc x st _ <- runSE p
                                 modify $ \s -> s { renv = M.insert (S r') (Just st) (renv s) }
                                 return $ TProc Nothing skip (TPid Nothing (Pid (Just r')))

symSpawnMany :: SymbEx RMulti -> SymbEx Int -> SymbEx (Process a) -> SymbEx (Process (Pid RMulti))
symSpawnMany r n p = SE $ do (TRoleMulti _ r') <- runSE r
                             m <- gets renv
                             case M.lookup (M r') m of
                               Just Nothing -> do
                                 TProc x st _ <- runSE p
                                 modify $ \s -> s { renv = M.insert (M r') (Just st) (renv s) }
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
            modify (\s -> s { renv = M.insert (S (RS n)) Nothing (renv s) })
            return (TProc Nothing skip (TRoleSing Nothing (RS n)))

-------------------------------------------------
symNewRMulti :: SymbEx (Process RMulti)
-------------------------------------------------
symNewRMulti
  = SE $ do n <- freshInt
            modify (\s -> s { renv = M.insert (M (RM n)) Nothing (renv s) })
            return (TProc Nothing skip (TRoleMulti Nothing (RM n)))

-------------------------------------------------
symDoMany :: SymbEx (Pid RMulti)
          -> SymbEx (Pid RSing -> Process a)
          -> SymbEx (Process ())
-------------------------------------------------
symDoMany p f
  = SE $ do v <- freshVar
            TPidMulti _ (Pid (Just (RM n))) <- runSE p
            TArrow _ g                 <- runSE f
            TProc _ s _                <- runSE (g (TPid (Just v) (Pid Nothing)))
            return (TProc Nothing (iter v n s) (TUnit Nothing))
    where
      iter v n s = IL.SIter (varToIL v) (IL.S $ "RM" ++ show n) s ()

-------------------------------------------------
symExec :: SymbEx (Process a)
        -> SymbEx a
-------------------------------------------------
symExec p
  = SE $ do (TProc _ st a) <- runSE p
            modify $ \s -> s {  renv = M.insert (me s) (Just st) (renv s) }
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

-------------------------------------------------
-- Instances
-------------------------------------------------
instance Symantics SymbEx where
  tt        = symtt
  repI      = symRep
  repS      = symRepS
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

instance (Recv a, AbsToIL a) => SymRecv SymbEx a where
  recv = symRecv

instance (Send a, AbsToIL a) => SymSend SymbEx a where
  send = symSend


emptyState :: SymbState
emptyState = SymbState { renv = M.empty
                       , ctr = 1
                       , me = S (RS 0)
                       }

runSymb :: SymbEx a -> SymbState
runSymb e = execState (runSE e) emptyState
