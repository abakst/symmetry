{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcFirewall where

import Prelude (($), undefined, String, Int, fromInteger, negate)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import Data.Either
import SrcHelper

type FWO = Int    :+:
           String

type Msg = (Pid RSing, Int) :+:  -- Call   Pid Int
           (Pid RSing, FWO)      -- Answer Pid FWO

class ( Symantics repr
      , SymSend   repr Msg
      , SymRecv   repr Msg
      , SymSend   repr FWO
      , SymRecv   repr FWO
      ) => FirewallSem repr

call_msg :: FirewallSem repr => repr (Pid RSing -> Int -> Msg)
call_msg  = lam $ \pid -> lam $ \i -> inl (pair pid i)

answer_msg :: FirewallSem repr => repr (Pid RSing -> FWO -> Msg)
answer_msg  = lam $ \pid -> lam $ \f -> inr (pair pid f)

recv_call :: FirewallSem repr => repr (Process (Pid RSing, Int))
recv_call  = do msg :: repr Msg <- recv
                ret $ match msg id fail

recv_answer :: FirewallSem repr => repr (Process (Pid RSing, FWO))
recv_answer  = do msg :: repr Msg <- recv
                  ret $ match msg fail id

firewall :: FirewallSem repr => repr (Process ())
firewall  = do l :: repr [Int] <- app any_list tt
               app start l

start :: FirewallSem repr => repr ([Int] -> Process ())
start  = lam $ \l -> do r_srv <- newRSing
                        srv <- spawn r_srv (app server pred)
                        r_fir <- newRSing
                        fir <- spawn r_fir (app server (app2 fw srv notZero))
                        app2 sendall fir l

sendall :: FirewallSem repr => repr (Pid RSing -> [Int] -> Process ())
sendall  = lam $ \to -> lam $ \l -> ifte (eq nil l) (ret tt) $
             let x  = hd l
                 xs = tl l
             in do me <- self
                   send to (app2 call_msg me x)
                   app2 sendall to xs

pred :: FirewallSem repr => repr (Int -> Process FWO)
pred  = lam $ \n -> ifte (eq n (repI 0)) (fail) (ret $ inl $ plus n (repI (-1)))

notZero :: FirewallSem repr => repr (Int -> Boolean)
notZero  = lam $ \n -> not (eq (repI 0) n)

server :: FirewallSem repr => repr ((Int -> Process FWO) -> Process ())
server  = lam $ \handle_call -> do me  <- self
                                   msg <- recv_call
                                   res <- app handle_call (proj2 msg)
                                   send (proj1 msg) (app2 answer_msg me res)
                                   app server handle_call

fw :: FirewallSem repr => repr (Pid RSing -> (Int -> Boolean) -> Int -> Process FWO)
fw  = lam $ \pr -> lam $ \t -> lam $ \x ->
        ifte (app t x)
          (do me <- self
              send pr (app2 call_msg me x)
              msg <- recv_answer
              ret $ proj2 msg)
          (ret $ inr $ repS "DON'T GIVE ME ZERO !!!")
