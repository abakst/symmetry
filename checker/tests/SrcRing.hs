{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcRing where

import Prelude (($), undefined, Int, fromInteger)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import SrcHelper

import GHC.Num ((+))
import Data.Either

class ( Symantics repr
      , SymSend   repr Msg
      , SymRecv   repr Msg
      ) => RingSem repr

type Msg = (Int,Pid RSing) :+:  -- Peek PeanoN ProcessId
           ([Int]          :+:  -- Ans  [PeanoN]
           ([Int]          ))   -- Forward [PeanoN]

msg_handler :: RingSem repr
            => repr (Msg -> ((Int,Pid RSing)->a) -> ([Int]->a) -> ([Int]->a) -> a)
msg_handler = lam $ \msg ->
              lam $ \ph -> lam $ \ah -> lam $ \fh ->
                match msg ph $ lam $ \e1 ->
                  match e1 ah fh

peek_msg :: RingSem repr => repr (Int -> Pid RSing -> Msg)
peek_msg  = lam $ \i -> lam $ \pid -> inl $ pair i pid

ans_msg :: RingSem repr => repr ([Int] -> Msg)
ans_msg  = lam $ \xs -> inr $ inl xs

recv_ans :: RingSem repr => repr (Process [Int])
recv_ans  = do msg::repr Msg <- recv
               ret (app (app (app (app msg_handler msg) fail) id) fail)

forward_msg :: RingSem repr => repr ([Int] -> Msg)
forward_msg  = lam $ \xs -> inr $ inr xs

ring :: RingSem repr => repr (Process ())
ring  = do xs :: repr [Int] <- app any_list tt
           p <- app (app init_ring slave) xs
           app probe_ring p


probe_ring :: RingSem repr => repr ((Pid RSing) -> Process ())
probe_ring  = lam $ \p -> do me <- self
                             send p (app (app peek_msg (repI 0)) me)
                             recv_ans
                             app probe_ring p


init_ring :: RingSem repr
          => repr ((Pid RSing -> Int -> Process ()) -> [Int] -> Process (Pid RSing))
init_ring  = lam $ \fun -> lam $ \xs ->
               do role <- newRSing
                  spawn role (app (app bootstrap_ring2 fun) xs)

bootstrap_ring2 :: RingSem repr
                => repr ((Pid RSing -> Int -> Process ()) -> [Int] -> Process ())
bootstrap_ring2  = lam $ \fun -> lam $ \xs ->
                     do me <- self
                        app (app (app bootstrap_ring3 fun) me) xs

bootstrap_ring3 :: RingSem repr
                => repr ((Pid RSing -> Int -> Process ()) -> (Pid RSing) -> [Int]
                         -> Process ())
bootstrap_ring3 = lam $ \fun -> lam $ \prev -> lam $ \xs ->
                    ifte (eq nil (tl xs))
                      (app (app fun prev) (hd xs))
                      (let x'  = hd xs
                           xs' = tl xs
                       in do r <- newRSing
                             nxt <- spawn r $ (app (app fun prev) x')
                             app (app (app bootstrap_ring3 fun) nxt) xs')

slave :: RingSem repr
      => repr (Pid RSing -> Int -> Process ())
slave = lam $ \nxt -> lam $ \me ->
          let fh = lam $ \xs -> send nxt (app forward_msg (cons me xs))
              ph = undefined
          in do msg :: repr Msg <- recv
                app (app (app (app msg_handler msg) ph) fail) fh
