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
      , SymMatch repr (Pid RSing) Int (Pid RSing)
      , SymMatch repr (Pid RSing) Int Int
      , SymTypes repr () ()
      , SymTypes repr (Pid RSing) Int
      ) => SieveSem repr

--instance SieveSem SymbEx

sieve_main :: SieveSem repr => repr (Process ())
sieve_main  = do me    <- self
                 r_gen <- newRSing
                 gen   <- spawn r_gen (app counter (repI 2))
                 r_s   <- newRSing
                 spawn r_s (app2 sieve gen me)
                 dump

dump :: SieveSem repr => repr (Process ())
dump  = do x :: repr Int <- recv
           app print x
           dump

counter :: SieveSem repr => repr (Int -> Process ())
counter  = lam $ \n -> do poke_from <- recv_poke
                          send poke_from (app ans_msg n)
                          app counter (plus n (repI 1))

sieve :: SieveSem repr => repr (Pid RSing -> Pid RSing -> Process ())
sieve  = lam $ \input -> lam $ \output ->
           do me <- self
              send input (app poke_msg me)
              x <- recv_ans
              send output x
              r <- newRSing
              f <- spawn r (app2 filter2 (app divisible_by x) input)
              app2 sieve f output

filter2 :: SieveSem repr
        => repr ((Int->Boolean) -> Pid RSing -> Process (Int->Boolean))
filter2  = lam $ \test -> lam $ \input -> do from <- recv_poke
                                             app3 filter3 test input from

filter3 :: SieveSem repr
        => repr ((Int->Boolean) -> Pid RSing -> Pid RSing ->
                 Process (Int->Boolean))
filter3  = lam $ \test -> lam $ \input -> lam $ \output ->
             do me <- self
                send input (app poke_msg me)
                y <- recv_ans
                ifte (app test y)
                  (app3 filter3 test input output)
                  (do send output (app ans_msg y)
                      app2 filter2 test input)

divisible_by :: SieveSem repr => repr (Int -> Int -> Boolean)
divisible_by = lam $ \x -> lam $ \y -> ifte (eq (app2 mod y x) (repI 0)) (inl tt) (inr tt)

