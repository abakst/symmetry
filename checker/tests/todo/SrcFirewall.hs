{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return, id, pred, not)
import Symmetry.Language
import Symmetry.Verify
import Symmetry.SymbEx
import SrcHelper

type FWO = Int    :+:
           String

type Msg = (Pid RSing, Int) :+:  -- Call   Pid Int
           (Pid RSing, FWO)      -- Answer Pid FWO

class ( HelperSym repr
      ) => FirewallSem repr

instance FirewallSem SymbEx

call_msg :: FirewallSem repr => repr (Pid RSing -> Int -> Msg)
call_msg  = lam $ \pid -> lam $ \i -> inl (pair pid i)

answer_msg :: FirewallSem repr => repr (Pid RSing -> FWO -> Msg)
answer_msg  = lam $ \pid -> lam $ \f -> inr (pair pid f)

recv_call :: FirewallSem repr => repr (Process repr (Pid RSing, Int))
recv_call  = do msg :: repr Msg <- recv
                match msg id reject

recv_answer :: FirewallSem repr => repr (Process repr (Pid RSing, FWO))
recv_answer  = do msg :: repr Msg <- recv
                  match msg reject id

firewall :: FirewallSem repr => repr (Process repr ())
firewall  = do l :: repr [Int] <- app any_list tt
               app start l

start :: FirewallSem repr => repr ([Int] -> Process repr ())
start  = lam $ \l -> do r_srv <- newRSing
                        srv <- spawn r_srv (app server pred)
                        r_fir <- newRSing
                        fir <- spawn r_fir (app server (app2 fw srv notZero))
                        app2 sendall fir l

type T_sa = (Pid RSing, [Int])
f_sendall :: FirewallSem repr
          => repr ((T_sa -> Process repr T_sa) -> T_sa -> Process repr T_sa)
f_sendall  = lam $ \sendall -> lam $ \arg ->
               do let to = proj1 arg
                  let l  = proj2 arg
                  matchList l (lam $ \_ -> ret arg) $
                    lam $ \ht -> let x  = proj1 ht
                                     xs = proj2 ht
                                  in do me <- self
                                        send to (app2 call_msg me x)
                                        app sendall $ pair to xs

sendall :: FirewallSem repr => repr (Pid RSing -> [Int] -> Process repr ())
sendall  = lam $ \to -> lam $ \l -> do app (fixM f_sendall) (pair to l)
                                       ret tt

pred :: FirewallSem repr => repr (Int -> Process repr FWO)
pred  = lam $ \n -> ifte (eq n (int 0)) (fail) (ret $ inl $ plus n (int (-1)))

notZero :: FirewallSem repr => repr (Int -> Boolean)
notZero  = lam $ \n -> not (eq (int 0) n)

server :: FirewallSem repr => repr ((Int -> Process repr FWO) -> Process repr ())
server  = lam $ \handle_call ->
            do let helper = lam $ \server -> lam $ \handle_call ->
                              do me  <- self
                                 msg <- recv_call
                                 res <- app handle_call (proj2 msg)
                                 send (proj1 msg) (app2 answer_msg me res)
                                 app server handle_call
               app (fixM helper) handle_call
               ret tt


fw :: FirewallSem repr => repr (Pid RSing -> (Int -> Boolean) -> Int -> Process repr FWO)
fw  = lam $ \pr -> lam $ \t -> lam $ \x ->
        ifte (app t x)
          (do me <- self
              send pr (app2 call_msg me x)
              msg <- recv_answer
              ret $ proj2 msg)
          (ret $ inr $ str "DON'T GIVE ME ZERO !!!")

main :: IO ()
main  = checkerMain $ exec firewall
