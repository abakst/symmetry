{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return, id, print, mod)
import Symmetry.Language
import Symmetry.Verify
import Symmetry.SymbEx
import SrcHelper

type Msg = (Pid RSing) :+:  -- Poke ProcessId
           Int              -- Ans  Int

poke_msg :: SieveSem repr => repr (Pid RSing -> Msg)
poke_msg  = lam $ \pid -> inl pid

ans_msg :: SieveSem repr => repr (Int -> Msg)
ans_msg  = lam $ \n -> inr n

recv_poke :: SieveSem repr => repr (Process repr (Pid RSing))
recv_poke  = do msg :: repr Msg <- recv
                match msg id reject

recv_ans :: SieveSem repr => repr (Process repr Int)
recv_ans  = do msg :: repr Msg <- recv
               match msg reject id

class ( HelperSym repr
      ) => SieveSem repr

instance SieveSem SymbEx

sieve_main :: SieveSem repr => repr (Process repr ())
sieve_main  = do me    <- self
                 r_gen <- newRSing
                 gen   <- spawn r_gen (app counter (int 2))
                 r_s   <- newRSing
                 spawn r_s (app2 sieve gen me)
                 dump

dump :: SieveSem repr => repr (Process repr ())
dump  = do let f_dump = lam $ \dump -> lam $ \_ ->
                          do x :: repr Int <- recv
                             app print x
                             app dump tt
           app (fixM f_dump) tt

counter :: SieveSem repr => repr (Int -> Process repr ())
counter  = lam $ \n ->
             do let f_counter = lam $ \counter -> lam $ \n ->
                                  do poke_from <- recv_poke
                                     send poke_from (app ans_msg n)
                                     app counter (plus n (int 1))
                app (fixM f_counter) n
                ret tt

sieve :: SieveSem repr => repr (Pid RSing -> Pid RSing -> Process repr ())
sieve  = lam $ \input -> lam $ \output ->
           do let f_sieve = lam $ \sieve -> lam $ \arg ->
                              do let input  = proj1 arg
                                     output = proj2 arg
                                 me <- self
                                 send input (app poke_msg me)
                                 x <- recv_ans
                                 send output x
                                 r <- newRSing
                                 f <- spawn r (app2 filter2 x input)
                                 app sieve $ pair f output
              app (fixM f_sieve) $ pair input output
              ret tt

type T_ar3 = () :+: Pid RSing
type T_f3  = (Int,(Pid RSing,T_ar3))

f_filter :: SieveSem repr
         => repr ((T_f3 -> Process repr T_f3) -> T_f3 -> Process repr T_f3)
f_filter  = lam $ \filter -> lam $ \arg ->
              do let test_n   = proj1 arg
                     input    = proj1 $ proj2 arg
                     m_output = proj2 $ proj2 arg
                 match m_output
                   (lam $ \_ ->
                      do from <- recv_poke -- filter2
                         app filter $ pair3 test_n input (inr from))
                   (lam $ \output ->
                      do me <- self -- filter3
                         send input (app poke_msg me)
                         y <- recv_ans
                         test_v <- app2 divisible_by test_n y
                         ifte test_v
                           (app filter $ pair3 test_n input (inr output))
                           (do send output (app ans_msg y)
                               app filter $ pair3 test_n input (inl tt)))

filter2 :: SieveSem repr
        => repr (Int -> Pid RSing -> Process repr ())
filter2  = lam $ \test_n -> lam $ \input ->
             do app (fixM f_filter) $ pair3 test_n input (inl tt)
                ret tt

divisible_by :: SieveSem repr
             => repr (Int -> Int -> Process repr Boolean)
divisible_by = lam $ \x -> lam $ \y ->
                 do r <- app2 mod y x
                    ifte (eq r (int 0))
                      (ret $ inl tt)
                      (ret $ inr tt)

main :: IO ()
main  = checkerMain $ exec sieve_main
