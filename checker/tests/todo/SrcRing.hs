{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcRing where

import Prelude (($), undefined, Int, fromInteger)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import SrcHelper
import Symmetry.SymbEx

import GHC.Num ((+))
import Data.Either

class ( Symantics repr
      , SymSend repr Msg
      , SymRecv repr Msg
      , SymMatch repr () () (Process ())
      , SymMatch repr () () (Process T_br3)
      , SymMatch repr (Int, Pid RSing) (Either [Int] [Int]) (Process ())
      , SymMatch repr (Int, Pid RSing) (Either [Int] [Int]) [Int]
      , SymMatch repr [Int] [Int] (Process ())
      , SymMatch repr [Int] [Int] [Int]
      , SymTypes repr (Int, Pid RSing) ([Int] :+: [Int])
      , SymTypes repr (Pid RSing -> Int -> Process ()) (Pid RSing, [Int])
      , SymTypes repr (Pid RSing) [Int]
      , SymTypes repr Int (Pid RSing)
      , SymTypes repr [Int] [Int]
      , SymMatch repr [Int] [Int] (Int, Pid RSing)
      , SymMatch repr (Int, Pid RSing) ([Int] :+: [Int]) (Int, Pid RSing)
      ) => RingSem repr

instance RingSem SymbEx

type Msg = (Int,Pid RSing) :+:  -- Peek PeanoN ProcessId
           ([Int]          :+:  -- Ans  [PeanoN]
           ([Int]          ))   -- Forward [PeanoN]

peek_msg :: RingSem repr => repr (Int -> Pid RSing -> Msg)
peek_msg  = lam $ \i -> lam $ \pid -> inl $ pair i pid

recv_peek :: RingSem repr => repr (Process (Int,Pid RSing))
recv_peek  = do msg :: repr Msg <- recv
                ret $ match3 msg id fail fail

ans_msg :: RingSem repr => repr ([Int] -> Msg)
ans_msg  = lam $ \xs -> inr $ inl xs

recv_ans :: RingSem repr => repr (Process [Int])
recv_ans  = do msg::repr Msg <- recv
               ret $ match3 msg fail id fail

forward_msg :: RingSem repr => repr ([Int] -> Msg)
forward_msg  = lam $ \xs -> inr $ inr xs

recv_fwd :: RingSem repr => repr (Process [Int])
recv_fwd  = do msg::repr Msg <- recv
               ret $ match3 msg fail fail id

ring :: RingSem repr => repr (Process ())
ring  = do xs :: repr [Int] <- app any_list tt
           p <- app2 init_ring slave xs
           app probe_ring p


probe_ring :: RingSem repr => repr ((Pid RSing) -> Process ())
probe_ring  = lam $ \p ->
                do let helper = lam $ \probe_ring -> lam $ \p ->
                                  do me <- self
                                     send p $ app2 peek_msg (repI 0) me
                                     recv_ans
                                     app probe_ring p
                   app (fixM helper) p
                   ret tt

init_ring :: RingSem repr
          => repr ((Pid RSing -> Int -> Process ()) -> [Int] -> Process (Pid RSing))
init_ring  = lam $ \fun -> lam $ \xs ->
               do role <- newRSing
                  spawn role $ app2 bootstrap_ring2 fun xs

bootstrap_ring2 :: RingSem repr
                => repr ((Pid RSing -> Int -> Process ()) -> [Int] -> Process ())
bootstrap_ring2  = lam $ \fun -> lam $ \xs ->
                     do me <- self
                        app3 bootstrap_ring3 fun me xs

type T_br3 = ((Pid RSing -> Int -> Process ()),(Pid RSing,[Int]))

f_bootstrap_ring3 :: RingSem repr
                  => repr ((T_br3 -> Process T_br3) -> T_br3 -> Process T_br3)
f_bootstrap_ring3 = lam $ \bootstrap_ring3 -> lam $ \arg ->
                      do let fun  = proj1 arg
                         let prev = proj1 $ proj2 arg
                         let xs   = proj2 $ proj2 arg
                         ifte (eq nil (tl xs))
                           (do app2 fun prev (hd xs)
                               ret arg)
                           (let x'  = hd xs
                                xs' = tl xs
                             in do r <- newRSing
                                   nxt <- spawn r $ app2 fun prev x'
                                   app bootstrap_ring3 $ pair3 fun nxt xs')

bootstrap_ring3 :: RingSem repr
                => repr ((Pid RSing -> Int -> Process ()) -> (Pid RSing) -> [Int]
                         -> Process ())
bootstrap_ring3 = lam $ \fun -> lam $ \prev -> lam $ \xs ->
                    do app (fixM f_bootstrap_ring3) $ pair3 fun prev xs
                       ret tt

slave :: RingSem repr
      => repr (Pid RSing -> Int -> Process ())
slave = lam $ \nxt -> lam $ \me ->
          let fh = lam $ \xs -> send nxt (app forward_msg (cons me xs))
              ph = lam $ \arg -> do let x    = proj1 arg
                                    let from = proj2 arg
                                    send nxt (app forward_msg (cons me (cons x nil)))
                                    f_msg <- recv_fwd
                                    send from (app ans_msg f_msg)
          in do msg :: repr Msg <- recv
                match3 msg ph fail fh
