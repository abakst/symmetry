{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcSieve where

import Prelude (($), undefined, String, Int, fromInteger, negate)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import Data.Either
import SrcHelper
import Symmetry.SymbEx

type Msg = (Pid RSing) :+:  -- Poke ProcessId
           Int              -- Ans  Int

poke_msg :: SieveSem repr => repr (Pid RSing -> Msg)
poke_msg  = lam $ \pid -> inl pid

ans_msg :: SieveSem repr => repr (Int -> Msg)
ans_msg  = lam $ \n -> inr n

recv_poke :: SieveSem repr => repr (Process (Pid RSing))
recv_poke  = do msg :: repr Msg <- recv
                return $ match msg id fail

recv_ans :: SieveSem repr => repr (Process Int)
recv_ans  = do msg :: repr Msg <- recv
               return $ match msg fail id

class ( Symantics repr
      , SymRecv   repr Int
      , SymSend   repr Int
      , SymRecv   repr Msg
      , SymSend   repr Msg
      , SymMatch repr () () (() :+: ())
      , SymMatch repr () () (Process (Int -> Boolean))
      , SymMatch repr () () (Process T_f3)
      , SymMatch repr () (Pid RSing) (Process T_f3)
      , SymMatch repr (Pid RSing) Int (Pid RSing)
      , SymMatch repr (Pid RSing) Int Int
      , SymTypes repr () ()
      , SymTypes repr () (Pid RSing)
      , SymTypes repr (Int -> Boolean) (Pid RSing, T_ar3)
      , SymTypes repr (Pid RSing) (Pid RSing)
      , SymTypes repr (Pid RSing) Int
      , SymTypes repr (Pid RSing) T_ar3
      ) => SieveSem repr

instance SieveSem SymbEx

sieve_main :: SieveSem repr => repr (Process ())
sieve_main  = do me    <- self
                 r_gen <- newRSing
                 gen   <- spawn r_gen (app counter (repI 2))
                 r_s   <- newRSing
                 spawn r_s (app2 sieve gen me)
                 dump

dump :: SieveSem repr => repr (Process ())
dump  = do let f_dump = lam $ \dump -> lam $ \_ ->
                          do x :: repr Int <- recv
                             app print x
                             app dump tt
           app (fixM f_dump) tt

counter :: SieveSem repr => repr (Int -> Process ())
counter  = lam $ \n ->
             do let f_counter = lam $ \counter -> lam $ \n ->
                                  do poke_from <- recv_poke
                                     send poke_from (app ans_msg n)
                                     app counter (plus n (repI 1))
                app (fixM f_counter) n
                ret tt

sieve :: SieveSem repr => repr (Pid RSing -> Pid RSing -> Process ())
sieve  = lam $ \input -> lam $ \output ->
           do let f_sieve = lam $ \sieve -> lam $ \arg ->
                              do let input  = proj1 arg
                                     output = proj2 arg
                                 me <- self
                                 send input (app poke_msg me)
                                 x <- recv_ans
                                 send output x
                                 r <- newRSing
                                 f <- spawn r (app2 filter2 (app divisible_by x) input)
                                 app sieve $ pair f output
              app (fixM f_sieve) $ pair input output
              ret tt

type T_ar3 = () :+: Pid RSing
type T_f3  = ((Int->Boolean),(Pid RSing,T_ar3))

f_filter :: SieveSem repr
         => repr ((T_f3 -> Process T_f3) -> T_f3 -> Process T_f3)
f_filter  = lam $ \filter -> lam $ \arg ->
              do let test     = proj1 arg
                     input    = proj1 $ proj2 arg
                     m_output = proj2 $ proj2 arg
                 match m_output
                   (lam $ \_ ->
                      do from <- recv_poke -- filter2
                         app filter $ pair3 test input (inr from))
                   (lam $ \output ->
                      do me <- self -- filter3
                         send input (app poke_msg me)
                         y <- recv_ans
                         ifte (app test y)
                           (app filter $ pair3 test input (inr output))
                           (do send output (app ans_msg y)
                               app filter $ pair3 test input (inl tt)))

filter2 :: SieveSem repr
        => repr ((Int->Boolean) -> Pid RSing -> Process ())
filter2  = lam $ \test -> lam $ \input ->
             do app (fixM f_filter) $ pair3 test input (inl tt)
                ret tt

divisible_by :: SieveSem repr => repr (Int -> Int -> Boolean)
divisible_by = lam $ \x -> lam $ \y -> ifte (eq (app2 mod y x) (repI 0)) (inl tt) (inr tt)

