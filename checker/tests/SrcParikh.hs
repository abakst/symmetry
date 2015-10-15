{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcParikh where

import Prelude (($), undefined, String)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import Data.Either

type Msg = (Pid RSing,String) :+: -- Init (Pid RSing) String
           (String :+:            -- Set String
           (Pid RSing :+:         -- Get (Pid RSing)
           (() :+:                -- Ok
            () )))                -- Bye

class ( Symantics repr
      , SymSend   repr Msg
      , SymRecv   repr Msg
      , SymSend   repr String
      , SymRecv   repr String
      ) => ParikhSem repr

msg_handler :: ParikhSem repr
            => repr (Msg -> ((Pid RSing,String)->a) -> (String->a) ->
                     (Pid RSing->a) -> (()->a) -> (()->a) -> a)
msg_handler = lam $ \msg ->
              lam $ \ih -> lam $ \sh -> lam $ \gh -> lam $ \oh -> lam $ \bh ->
                match msg ih $ lam $ \e1 ->
                  match e1 sh $ lam $ \e2 ->
                  match e2 gh $ lam $ \e3 ->
                  match e3 oh bh

recv_init :: ParikhSem repr => repr (Process (Pid RSing, String))
recv_init  = do (msg::repr Msg) <- recv
                ret $ app (app (app (app (app (app msg_handler msg) id) fail) fail) fail) fail

init_msg :: ParikhSem repr => repr (Pid RSing -> String -> Msg)
init_msg  = lam $ \pid -> lam $ \s -> inl (pair pid s)

recv_set :: ParikhSem repr => repr (Process String)
recv_set  = do (msg::repr Msg) <- recv
               ret $ app (app (app (app (app (app msg_handler msg) fail) id) fail) fail) fail

set_msg :: Symantics repr => repr (String -> Msg)
set_msg  = lam $ \s -> inr (inl s)

recv_get :: ParikhSem repr => repr (Process (Pid RSing))
recv_get  = do (msg::repr Msg) <- recv
               ret $ app (app (app (app (app (app msg_handler msg) fail) fail) id) fail) fail

get_msg :: Symantics repr => repr (Pid RSing -> Msg)
get_msg  = lam $ \p -> inr $ inr $ inl p

recv_ok :: ParikhSem repr => repr (Process())
recv_ok  = do (msg::repr Msg) <- recv
              ret $ app (app (app (app (app (app msg_handler msg) fail) fail) fail) id) fail

ok_msg :: Symantics repr => repr Msg
ok_msg  = inr $ inr $ inr $ inl tt

recv_bye :: ParikhSem repr => repr (Process())
recv_bye  = do (msg::repr Msg) <- recv
               ret $ app (app (app (app (app (app msg_handler msg) fail) fail) fail) fail) id

bye_msg :: Symantics repr => repr Msg
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
do_serve  = lam $ \s -> let init_h = lam $ \_ -> fail
                            set_h  = lam $ \s' -> app do_serve s'
                            get_h  = lam $ \p -> do send p s
                                                    app do_serve s
                            bye_h  = lam $ \_ -> die
                            ok_h   = lam $ \_ -> fail
                         in do (msg::repr Msg) <- recv
                               ret tt
                               app (app (app (app (app (app msg_handler msg) init_h)
                                                                             set_h)
                                                                             get_h)
                                                                             ok_h)
                                                                             bye_h
