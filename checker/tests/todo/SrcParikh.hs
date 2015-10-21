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
      , SymRecv  repr Msg
      , SymRecv  repr String
      , SymSend  repr Msg
      , SymSend  repr String
      , SymMatch repr () () ()
      , SymMatch repr () () (Pid RSing)
      , SymMatch repr () () (Pid RSing, String)
      , SymMatch repr () () (Process ())
      , SymMatch repr () () (Process String)
      , SymMatch repr () () String
      , SymMatch repr (Pid RSing) (() :+: ()) ()
      , SymMatch repr (Pid RSing) (() :+: ()) (Pid RSing)
      , SymMatch repr (Pid RSing) (() :+: ()) (Pid RSing, String)
      , SymMatch repr (Pid RSing) (() :+: ()) (Process ())
      , SymMatch repr (Pid RSing) (() :+: ()) (Process String)
      , SymMatch repr (Pid RSing) (() :+: ()) String
      , SymMatch repr (Pid RSing, String) (String :+: (Pid RSing :+: (() :+: ()))) ()
      , SymMatch repr (Pid RSing, String) (String :+: (Pid RSing :+: (() :+: ()))) (Pid RSing)
      , SymMatch repr (Pid RSing, String) (String :+: (Pid RSing :+: (() :+: ()))) (Pid RSing, String)
      , SymMatch repr (Pid RSing, String) (String :+: (Pid RSing :+: (() :+: ()))) (Process ())
      , SymMatch repr (Pid RSing, String) (String :+: (Pid RSing :+: (() :+: ()))) (Process String)
      , SymMatch repr (Pid RSing, String) (String :+: (Pid RSing :+: (() :+: ()))) String
      , SymMatch repr String ((Pid RSing) :+: (() :+: ())) (Process String)
      , SymMatch repr String (Pid RSing :+: (() :+: ())) ()
      , SymMatch repr String (Pid RSing :+: (() :+: ())) (Pid RSing)
      , SymMatch repr String (Pid RSing :+: (() :+: ())) (Pid RSing, String)
      , SymMatch repr String (Pid RSing :+: (() :+: ())) (Process ())
      , SymMatch repr String (Pid RSing :+: (() :+: ())) String
      , SymTypes repr () ()
      , SymTypes repr (Pid RSing) (() :+: ())
      , SymTypes repr (Pid RSing) String
      , SymTypes repr (Pid RSing, String) (String :+: (Pid RSing :+: (() :+: ())))
      , SymTypes repr String (Pid RSing :+: (() :+: ()))
      ) => ParikhSem repr

instance ParikhSem SymbEx

recv_init :: ParikhSem repr => repr (Process (Pid RSing, String))
recv_init  = do (msg::repr Msg) <- recv
                ret $ match5 msg id fail fail fail fail

init_msg :: ParikhSem repr => repr (Pid RSing -> String -> Msg)
init_msg  = lam $ \pid -> lam $ \s -> inl (pair pid s)

recv_set :: ParikhSem repr => repr (Process String)
recv_set  = do (msg::repr Msg) <- recv
               ret $ match5 msg fail id fail fail fail

set_msg :: ParikhSem repr => repr (String -> Msg)
set_msg  = lam $ \s -> inr (inl s)

recv_get :: ParikhSem repr => repr (Process (Pid RSing))
recv_get  = do (msg::repr Msg) <- recv
               ret $ match5 msg fail fail id fail fail

get_msg :: ParikhSem repr => repr (Pid RSing -> Msg)
get_msg  = lam $ \p -> inr $ inr $ inl p

recv_ok :: ParikhSem repr => repr (Process())
recv_ok  = do (msg::repr Msg) <- recv
              ret $ match5 msg fail fail fail id fail

ok_msg :: ParikhSem repr => repr Msg
ok_msg  = inr $ inr $ inr $ inl tt

recv_bye :: ParikhSem repr => repr (Process())
recv_bye  = do (msg::repr Msg) <- recv
               ret $ match5 msg fail fail fail fail id

bye_msg :: ParikhSem repr => repr Msg
bye_msg  = inr $ inr $ inr $ inr tt

parikh_main :: ParikhSem repr => repr ()
parikh_main  = exec $ do serverRole <- newRSing
                         s  <- spawn serverRole server
                         me <- self
                         send s $ (app (app init_msg me) (repS "a"))
                         recv_ok
                         send s (app set_msg (repS "b"))
                         send s bye_msg
                         return tt

server :: ParikhSem repr => repr (Process ())
server  = do init_msg <- recv_init
             send (proj1 init_msg) ok_msg
             app do_serve (proj2 init_msg)

cons :: ParikhSem repr => repr (a->b->a)
cons = lam $ \a -> lam $ \b -> a

do_serve :: ParikhSem repr => repr (String -> Process ())
do_serve  = lam $ \s ->
  do let helper = lam $ \do_serve -> lam $ \s ->
                    do let init_h = lam $ \_ -> fail
                       let set_h = lam $ \s' -> app do_serve s'
                       let get_h = lam $ \p -> do send p s
                                                  app do_serve s
                       let bye_h = lam $ \_ -> die
                       let ok_h = lam $ \_ -> fail
                       msg :: repr Msg <- recv
                       match5 msg init_h set_h get_h ok_h bye_h
     app (fixM helper) s
     ret tt
