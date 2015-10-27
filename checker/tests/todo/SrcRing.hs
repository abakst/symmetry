{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return, id)
import Symmetry.Language
import Symmetry.Verify
import Symmetry.SymbEx
import SrcHelper

import Data.Either

class ( HelperSym repr
      ) => RingSem repr

instance RingSem SymbEx

type Msg = (Int,Pid RSing) :+:  -- Peek PeanoN ProcessId
           ([Int]          :+:  -- Ans  [PeanoN]
           ([Int]          ))   -- Forward [PeanoN]

peek_msg :: RingSem repr => repr (Int -> Pid RSing -> Msg)
peek_msg  = lam $ \i -> lam $ \pid -> inl $ pair i pid

recv_peek :: RingSem repr => repr (Process repr (Int,Pid RSing))
recv_peek  = do msg :: repr Msg <- recv
                match3 msg id reject reject

ans_msg :: RingSem repr => repr ([Int] -> Msg)
ans_msg  = lam $ \xs -> inr $ inl xs

recv_ans :: RingSem repr => repr (Process repr [Int])
recv_ans  = do msg::repr Msg <- recv
               match3 msg reject id reject

forward_msg :: RingSem repr => repr ([Int] -> Msg)
forward_msg  = lam $ \xs -> inr $ inr xs

recv_fwd :: RingSem repr => repr (Process repr [Int])
recv_fwd  = do msg::repr Msg <- recv
               match3 msg reject reject id

ring :: RingSem repr => repr (Process repr ())
ring  = do xs :: repr [Int] <- app any_list tt
           p <- app2 init_ring slave xs
           app probe_ring p


probe_ring :: RingSem repr => repr ((Pid RSing) -> Process repr ())
probe_ring  = lam $ \p ->
                do let helper = lam $ \probe_ring -> lam $ \p ->
                                  do me <- self
                                     send p $ app2 peek_msg (int 0) me
                                     recv_ans
                                     app probe_ring p
                   app (fixM helper) p
                   ret tt

init_ring :: RingSem repr
          => repr ((Pid RSing -> Int -> Process repr ()) -> [Int] -> Process repr (Pid RSing))
init_ring  = lam $ \fun -> lam $ \xs ->
               do role <- newRSing
                  spawn role $ app2 bootstrap_ring2 fun xs

bootstrap_ring2 :: RingSem repr
                => repr ((Pid RSing -> Int -> Process repr ()) -> [Int] -> Process repr ())
bootstrap_ring2  = lam $ \fun -> lam $ \xs ->
                     do me <- self
                        app3 bootstrap_ring3 fun me xs

type T_br3 repr = ((Pid RSing -> Int -> Process repr ()),(Pid RSing,[Int]))

f_bootstrap_ring3 :: RingSem repr
                  => repr ((T_br3 repr -> Process repr (T_br3 repr))
                           -> T_br3 repr -> Process repr (T_br3 repr))
f_bootstrap_ring3 = lam $ \bootstrap_ring3 -> lam $ \arg ->
                      do let fun  = proj1 arg
                         let prev = proj1 $ proj2 arg
                         let xs   = proj2 $ proj2 arg
                         matchList xs reject
                           (lam $ \ht ->
                             let hd = proj1 ht
                                 tl = proj2 ht
                              in matchList tl
                                 (lam $ \_ -> do app2 fun prev hd
                                                 ret arg)
                                 (lam $ \_ ->
                                    let x'  = hd
                                        xs' = tl
                                     in do r <- newRSing
                                           nxt <- spawn r $ app2 fun prev x'
                                           app bootstrap_ring3 $ pair3 fun nxt xs'))

bootstrap_ring3 :: RingSem repr
                => repr ((Pid RSing -> Int -> Process repr ()) -> (Pid RSing) -> [Int]
                         -> Process repr ())
bootstrap_ring3 = lam $ \fun -> lam $ \prev -> lam $ \xs ->
                    do app (fixM f_bootstrap_ring3) $ pair3 fun prev xs
                       ret tt

slave :: RingSem repr
      => repr (Pid RSing -> Int -> Process repr ())
slave = lam $ \nxt -> lam $ \me ->
          let fh = lam $ \xs -> send nxt (app forward_msg (cons me xs))
              ph = lam $ \arg -> do let x    = proj1 arg
                                    let from = proj2 arg
                                    send nxt (app forward_msg (cons me (cons x nil)))
                                    f_msg <- recv_fwd
                                    send from (app ans_msg f_msg)
          in do msg :: repr Msg <- recv
                match3 msg ph reject fh

main :: IO ()
main  = checkerMain $ exec ring
