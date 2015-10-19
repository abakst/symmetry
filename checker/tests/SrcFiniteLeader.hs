{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcFiniteLeader where

import Prelude (($), undefined, String, Int, fromInteger, negate)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import Data.Either
import SrcHelper

type MyDat = () :+: (() :+: ()) -- A | B | C
type ECM   = () :+: ()          -- Elected | Congratulations
type Out   = Pid RSing          -- Out Pid

elected_msg :: FLSem repr => repr ECM
elected_msg  = inl tt

recv_elected :: FLSem repr => repr (Process ())
recv_elected  = do msg :: repr ECM <- recv
                   ret $ match msg id fail

recv_out :: FLSem repr => repr (Process (Pid RSing))
recv_out  = do msg :: repr (Pid RSing) <- recv
               ret msg
out_msg :: FLSem repr => repr (Pid RSing -> Out)
out_msg  = id

a_msg :: FLSem repr => repr (MyDat)
a_msg = inl tt
b_msg :: FLSem repr => repr (MyDat)
b_msg = inr $ inl tt
c_msg :: FLSem repr => repr (MyDat)
c_msg = inr $ inr tt

congrats_msg :: FLSem repr => repr ECM
congrats_msg  = inr tt

class ( Symantics repr
      , SymRecv   repr MyDat
      , SymSend   repr MyDat
      , SymRecv   repr ECM
      , SymSend   repr ECM
      , SymRecv   repr Out
      , SymSend   repr Out
      ) => FLSem repr

finite_leader :: FLSem repr => repr (Process ())
finite_leader  = do testtnode
                    ret tt

testtnode :: FLSem repr => repr (Process ECM)
testtnode = app start (lam $ \out -> lam $ \notary -> lam $ \x -> app3 tnode out notary x)

testsnode :: FLSem repr => repr (Process ECM)
testsnode = app start (lam $ \out -> lam $ \notary -> lam $ \x -> app3 snode out notary x)

testdnode :: FLSem repr => repr (Process ECM)
testdnode = app start (lam $ \out -> lam $ \notary -> lam $ \x -> app3 dnode out notary x)

type FunT = Pid RSing -> Pid RSing -> MyDat -> Process ()

start :: FLSem repr => repr (FunT -> Process ECM)
start  = lam $ \f -> do me <- self
                        app2 ring_abc f me
                        recv_elected
                        ret congrats_msg


ring_abc :: FLSem repr => repr (FunT -> Pid RSing -> Process ())
ring_abc  = lam $ \fun -> lam $ \notary ->
              do r1 <- newRSing
                 a  <- spawn r1 $ do out <- recv_out
                                     app3 fun out notary a_msg
                 r2 <- newRSing
                 b  <- spawn r2 (app3 fun a notary b_msg)
                 r3 <- newRSing
                 c  <- spawn r3 (app3 fun b notary c_msg)
                 send a (app out_msg c)

init_ring :: FLSem repr => repr (FunT -> [MyDat] -> Pid RSing -> Process (Pid RSing))
init_ring  = lam $ \fun -> lam $ \l -> lam $ \notary ->
               do r <- newRSing
                  pnew <- spawn r $ do out <- recv_out
                                       app3 fun out notary (hd l)
                  app5 ring fun (tl l) notary pnew pnew

ring :: FLSem repr
     => repr (FunT -> [MyDat] -> Pid RSing -> Pid RSing -> Pid RSing
              -> Process (Pid RSing))
ring  = lam $ \fun -> lam $ \l -> lam $ \notary -> lam $ \pstop -> lam $ \pprev ->
          ifte (eq l nil)
            (do send pstop (app out_msg pprev)
                ret pstop)
            (do r <- newRSing
                pnew <- spawn r (app3 fun pprev notary (hd l))
                app5 ring fun (tl l) notary pstop pnew)

-- first alg

tnode :: FLSem repr => repr (Pid RSing -> Pid RSing -> MyDat -> Process ())
tnode  = lam $ \out -> lam $ \notary -> lam $ \d ->
           do send out d
              app3 tnodeB out notary d

tnodeB :: FLSem repr => repr (Pid RSing -> Pid RSing -> MyDat -> Process ())
tnodeB  = lam $ \out -> lam $ \notary -> lam $ \d ->
            do e :: repr MyDat <- recv
               match3 (app2 compare e d)
                 (lam $ \_ -> app3 tnodeB out notary d)
                 (lam $ \_ -> send notary elected_msg)
                 (lam $ \_ -> app3 tnode out notary e)

snode :: FLSem repr => repr (Pid RSing -> Pid RSing -> MyDat -> Process ())
snode  = lam $ \out -> lam $ \notary -> lam $ \d ->
           do send out d
              e :: repr MyDat <- recv
              match3 (app2 compare e d)
                (lam $ \_ -> app c out)
                (lam $ \_ -> send notary elected_msg)
                (lam $ \_ -> app3 snode out notary e)

c :: FLSem repr => repr (Pid RSing -> Process ())
c  = lam $ \out -> do v :: repr MyDat <- recv
                      send out v
                      app c out

dnode :: FLSem repr => repr (Pid RSing -> Pid RSing -> MyDat -> Process ())
dnode  = lam $ \out -> lam $ \notary -> lam $ \d ->
           do send out d
              e :: repr MyDat <- recv
              let handler = lam $ \_ -> do send out e
                                           f :: repr MyDat <- recv
                                           ifte (and (gt e d) (gt e f))
                                             (app3 dnode out notary e)
                                             (app c out)
               in match3 (app2 compare e d)
                    handler
                    (lam $ \_ -> send notary elected_msg)
                    handler
