{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, DeriveGeneric #-}
{-# OPTIONS_GHC -Wall #-}
import Control.Distributed.Process hiding (Message)
import Control.Distributed.Process.Closure

import Control.Monad
import Text.Printf
import GHC.Generics (Generic)
import Data.Binary
import Data.Typeable

import DistribUtils

data Message = Ping ProcessId
             | Pong ProcessId
  deriving (Typeable, Generic)

type Pid = ProcessId {- PidClass -}

instance Binary Messaged

{-
P ::= 0
    | c(x).P
    | c<x>
    | case x of {B -> P}
    | (P | x ▹ Q)
    | new(x) P

[[ P < A > () ]] ~ (new(k) A | k(x).0)

(new(k)(P.k<x> | k<x>.Q)) ⇒ (P.Q) whenever k not in P, Q
-}

{-
expect     :: P < me(T)(x).k<x> > T 

send       :: p:Pid 
           -> x:T 
           -> P < p(T)<T>.k<()> > ()

getSelfPid :: P < k<me> > Pid

spawn      :: P < A > ()
           -> P < new(x) (k<x> || x : new(k)A) > Pid

???
forM       :: xs:[a]
           -> (a -> P < A > b)
           -> P < (R 0 (λi.λX. (new(k)(A || k<x>.X))))  xs > [b]

(>>=)      :: P < A > a
           -> (x:a -> P < B > b)
           -> P < new(k) (A.k<x> || k(x).B) > b
-}


{-
Recv [ (mPing (pvar "x"), Send (pvar "x") [(mPong me, Skip ())] ())
      , (mPong (pvar "x"), Skip ())
      ] ()
-}

-- pingServer :: P < me(T)(x).case x of { Ping from -> from(Message)(Message @ Pong me).k<()>
--                                      ; _         -> die
--                                      }
--                 > ()
pingServer :: Process ()
pingServer = 
  -- do
  -- Ping from <- expect
  -- P < new(k)(me(T)(x).k<x> || k(x).case x of { Ping from -> ... }... > ()
  -- Which should be equivalent to:
  -- P < me(T)(x).case x of { Ping from -> from(Message)(Message @ Pong me).k<()>
  --                        ; _         -> die
  --                        }
  --   > ()
  expect -- P < me(T)(x).k<x> > Message
  >>=
  \p ->
    -- P < case p of { Ping from -> ...; _ -> die.k<()> } > 
    case p of
      Ping from -> 
      -- P < new(k)(k<()> || k(x).(new(k)(k<me> || k(me).from(Message)(Messagae @ Pong me)).k<()>)) > ()
        -- P < k<()> > ()
        say $ printf "ping received from %s" (show from)
        -- P < k<me> > Pid
        mypid <- getSelfPid                             
        -- P < from(Message)(Message @ Pong mypid).k<()> > ()
        send from (Pong mypid)                          
      Pong from ->
        error "AH!"
    return ()
         

remotable ['pingServer]

{-
Block [ Iter (V "pi") (S "ps")
           (Send (pvar "pi") [(mPing tpid0, Skip ())] ()) ()
       , Iter (V "pii") (S "ps")
           (Recv [(mPong (pvar "x"), Skip ())] ()) ()] ()
-}
master :: [NodeId] -> Process ()
master peers = do
  ps <- forM peers $ \nid -> do
          say $ printf "spawning on %s" (show nid)
          -- P < Spawn(PingServer) > Pid
          spawn nid $(mkStaticClosure 'pingServer)

  mypid <- getSelfPid

  forM_ ps $ \pid -> do
    say $ printf "pinging %s" (show pid)
    send pid (Ping mypid)

  waitForPongs ps

  say "All pongs successfully received"
  terminate
  
waitForPongs :: [ProcessId] -> Process ()
waitForPongs [] = return ()
waitForPongs ps = do
  m <- expect
  case m of
    Pong p -> waitForPongs (filter (/= p) ps)
    _  -> say "MASTER received ping" >> terminate

waitForPongs' :: [ProcessId] -> Process ()
waitForPongs' = 
  forM_ ps $ const $ do { Pong _ <- expect; return () }

main :: IO ()
main = distribMain master Main.__remoteTable
