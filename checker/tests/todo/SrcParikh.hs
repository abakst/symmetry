{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcParikh where

import Prelude (($), undefined, String)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import Data.Either
import SrcHelper
import Symmetry.SymbEx

type Msg = (Pid RSing,String) :+: -- Init (Pid RSing) String
           (String :+:            -- Set String
           (Pid RSing :+:         -- Get (Pid RSing)
           (() :+:                -- Ok
            () )))                -- Bye

class ( Symantics repr
      , ArbPat repr String
      , ArbPat repr (Pid RSing, String)
      , ArbPat repr (Pid RSing)
      , ArbPat repr ()
      ) => ParikhSem repr

instance ParikhSem SymbEx

recv_init :: ParikhSem repr => repr (Process repr (Pid RSing, String))
recv_init  = do msg::repr Msg <- recv
                match5 msg id reject reject reject reject

init_msg :: ParikhSem repr => repr (Pid RSing -> String -> Msg)
init_msg  = lam $ \pid -> lam $ \s -> inl (pair pid s)

recv_set :: ParikhSem repr => repr (Process repr String)
recv_set  = do msg :: repr Msg <- recv
               match5 msg reject id reject reject reject

set_msg :: ParikhSem repr => repr (String -> Msg)
set_msg  = lam $ \s -> inr (inl s)

recv_get :: ParikhSem repr => repr (Process repr (Pid RSing))
recv_get  = do (msg::repr Msg) <- recv
               match5 msg reject reject id reject reject

get_msg :: ParikhSem repr => repr (Pid RSing -> Msg)
get_msg  = lam $ \p -> inr $ inr $ inl p

recv_ok :: ParikhSem repr => repr (Process repr())
recv_ok  = do (msg::repr Msg) <- recv
              match5 msg reject reject reject id reject

ok_msg :: ParikhSem repr => repr Msg
ok_msg  = inr $ inr $ inr $ inl tt

recv_bye :: ParikhSem repr => repr (Process repr())
recv_bye  = do (msg::repr Msg) <- recv
               match5 msg reject reject reject reject id

bye_msg :: ParikhSem repr => repr Msg
bye_msg  = inr $ inr $ inr $ inr tt

parikh_main :: ParikhSem repr => repr ()
parikh_main  = exec $ do serverRole <- newRSing
                         s  <- spawn serverRole server
                         me <- self
                         send s $ (app (app init_msg me) (str "a"))
                         recv_ok
                         send s (app set_msg (str "b"))
                         send s bye_msg
                         return tt

server :: ParikhSem repr => repr (Process repr ())
server  = do init_msg <- recv_init
             send (proj1 init_msg) ok_msg
             app do_serve (proj2 init_msg)

cons :: ParikhSem repr => repr (a->b->a)
cons = lam $ \a -> lam $ \b -> a

do_serve :: ParikhSem repr => repr (String -> Process repr ())
do_serve  = lam $ \s ->
  do let helper = lam $ \do_serve -> lam $ \s ->
                    do let init_h = reject
                       let set_h = lam $ \s' -> app do_serve s'
                       let get_h = lam $ \p -> do send p s
                                                  app do_serve s
                       let bye_h = lam $ \_ -> die
                       let ok_h = reject
                       msg :: repr Msg <- recv
                       match5 msg init_h set_h get_h ok_h bye_h
     app (fixM helper) s
     ret tt
