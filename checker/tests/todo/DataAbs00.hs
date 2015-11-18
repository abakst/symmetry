{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return, id, lookup)
import Symmetry.Language
import Symmetry.Verify
import Symmetry.SymbEx
import SrcHelper

type Msg = Int

sender :: DSL repr => repr (Pid RSing -> Process repr ())
sender  = lam $ \pid -> send pid (int 0)

receiver :: DSL repr => repr (Process repr ())
receiver  = do msg :: repr Msg <- recv
               ifte (eq msg (int 0)) (return tt) (fail)

master :: DSL repr => repr (Process repr ())
master  = do r_rec <- newRSing
             rec_pid <- spawn r_rec receiver
             r_sender <- newRSing
             spawn r_sender (app sender rec_pid)
             ret tt

main :: IO ()
main  = checkerMain $ exec master
