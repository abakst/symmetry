{-# Language TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, GADTs #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing  #-}
module SymbEx where

import           Data.Hashable  
import qualified Data.HashMap.Strict as M
import           Control.Monad.State
import           Control.Monad.Identity
import           Language.AST as L
import qualified AST          as IL

data Var   = V Int deriving Show
v (V i) = "x" ++ show i

type Env  = M.HashMap Var AbsVal
type REnv = M.HashMap Role (Maybe (IL.Stmt ()))
data Role = S RSing
          | M RMulti
            deriving (Eq, Show)

instance Hashable Role where
  hashWithSalt s (S r) = hashWithSalt s r
  hashWithSalt s (M r) = hashWithSalt s r

data SymbState = SymbState { env  :: Env
                           , renv :: REnv
                           , stmt :: IL.Stmt ()
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
            
data SymbEx a = SE { runSE :: SymbExM (Abs a) } -- StateT SymbState Identity (Abs a) }

data Abs t where
  TUnit :: Maybe Var -> Abs ()
  TInt :: Maybe Var -> Abs Int
  TPid :: Maybe Var -> L.Pid (Maybe RSing) -> Abs (Pid RSing)
  TRoleSing :: Maybe Var -> RSing -> Abs RSing
  TString :: Maybe Var -> Abs String
  TArrow :: Maybe Var -> (Abs a -> SymbEx b) -> Abs (a -> b)
  TProc :: Maybe Var -> Abs a -> Abs (L.Process a)

data AbsVal = AUnit (Abs ())
            | AInt (Abs Int)
            | APid (Abs (Pid RSing))
            | ARoleSing (Abs RSing)
            | AString (Abs String)
            | AFun AbsVal AbsVal
            | AProc AbsVal

class Recv t where
  recvTy :: Maybe Var -> Abs t

class Send t where
  -- This line intentionally left blank

instance Recv (Pid RSing) where
  recvTy v = TPid v (Pid Nothing)

instance Send (Pid RSing) where
  -- This line intentionally left blank

instance Send (()) where
  -- This line intentionally left blank

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

seqStmtM :: IL.Stmt () -> SymbExM ()
seqStmtM t = modify $ \s -> s { stmt = stmt s `seqStmt` t }

-------------------------------------------------
-- | Updates to roles
-------------------------------------------------
-- lookupRoleM r = do m <- gets renv

spawnSingle :: SymbEx RSing -> SymbEx (Process a) -> SymbEx (Process (Pid RSing))
spawnSingle r p = SE $ do (TRoleSing _ r') <- runSE r
                          m <- gets renv
                          case M.lookup (S r') m of
                            Just Nothing -> do sOld <- get
                                               modify $ \s -> s { stmt = IL.SSkip ()
                                                                , me   = S r'
                                                                }
                                               runSE p
                                               st <- gets stmt
                                               modify $ \s -> s { stmt = stmt sOld
                                                                , me   = me sOld
                                                                , renv = M.insert (S r') (Just st) (renv sOld)
                                                                }
                                               return $ TProc Nothing (TPid Nothing (Pid (Just r')))
                                     
             
-------------------------------------------------
-- | The Syntax-directed Symbolic Execution
-------------------------------------------------
instance Symantics SymbEx where
  tt     = SE . return $ TUnit Nothing
  repS _ = SE . return $ TString Nothing

  lam f = SE . return $ TArrow Nothing $ \a -> f (SE $ return a)

  app (SE e1) (SE e2) = SE $ do e1' <- e1
                                case e1' of
                                  TArrow _ f -> do e2' <- e2
                                                   runSE (f e2')

  self         = SE $ do S r <- gets me
                         return . TProc Nothing $ TPid Nothing (Pid (Just r))

  bind mm mf   = SE $ do TProc _ a  <- runSE mm
                         TArrow _ f <- runSE mf
                         runSE $ f a

  spawn        = spawnSingle

  exec p       = SE $ do (TProc _ a) <- runSE p
                         modify $ \s -> s { stmt = IL.SSkip ()
                                          , renv = M.insert (me s) (Just $ stmt s) (renv s)
                                          }
                         return a
                         
  ret x        = SE $ do a <- runSE x
                         return (TProc Nothing a)

  newRSing = SE $ do n <- freshInt
                     modify (\s -> s { renv = M.insert (S (RS n)) Nothing (renv s) })
                     return (TProc Nothing (TRoleSing Nothing (RS n)))


instance (Recv a, AbsToIL a) => SymRecv SymbEx a where
  recv         = SE $ do x <- freshVar
                         let tr = recvTy (Just x)
                         seqStmtM $ recvToIL tr
                         return $ TProc Nothing tr

instance (Send a, AbsToIL a) => SymSend SymbEx a where
  send pidM mM = SE $ do p <- runSE pidM
                         m <- runSE mM
                         seqStmtM $ sendToIL p m
                         return (TProc Nothing (TUnit Nothing))


emptyState :: SymbState
emptyState = SymbState { env = M.empty
                       , renv = M.empty
                       , stmt = IL.SSkip ()
                       , ctr = 1
                       , me = S (RS 0)
                       }

runSymb :: SymbEx a -> SymbState
runSymb e = execState (runSE e) emptyState
