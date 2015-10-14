{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
module SrcParikh where

import Prelude (($), undefined, String)
import Language.AST
import Language.Syntax
import Data.Either

data Init = Init
data Set  = Set
data Get  = Get
data Ok   = Ok
data Bye  = Bye

type Init_t = (Init,(Pid RSing,String))
type Set_t  = (Set,String)
type Get_t  = (Get,Pid RSing)

init_msg      :: Symantics repr => repr (Pid RSing) -> String -> repr Init_t
init_msg pid a = pair (repAny Init) (pair pid (repAny a))

set_msg  :: Symantics repr => String -> repr Set_t
set_msg s = pair (repAny Set) (repS s)

get_msg    :: Symantics repr => repr (Pid RSing) -> repr Get_t
get_msg pid = pair (repAny Get) pid

bye_msg :: Symantics repr => repr Bye
bye_msg  = repAny Bye

ok_msg :: Symantics repr => repr Ok
ok_msg  = repAny Ok

parikh_main :: ParikhSemantics repr => repr ()
parikh_main  = exec $ do serverRole <- newRSing
                         s  <- spawn serverRole server
                         me <- self
                         send s $ init_msg me "a"
                         msg :: repr Ok <- recv
                         send s (set_msg "b")
                         send s bye_msg
                         return tt

server :: ParikhSemantics repr => repr (Process ())
server  = do msg :: repr (Init,(Pid RSing, String)) <- recv
             send (proj1 $ proj2 msg) ok_msg
             do_serve (proj2 $ proj2 msg)

type Do_serve_t = Either Init_t (Either Set_t (Either Get_t Bye))

do_serve  :: ParikhSemantics repr
          => repr String -> repr (Process ())
do_serve s = let init_handler = lam $ \(msg::repr Init_t) -> fail_proc
                 set_handler  = lam $ \(msg::repr Set_t)  -> do_serve (proj2 msg)
                 get_handler  = lam $ \(msg::repr Get_t)  -> do send (proj2 msg) s
                                                                do_serve s
                 bye_handler  = lam $ \(msg::repr Bye)    -> die
              in do (msg :: repr Do_serve_t)  <- recv
                    match msg init_handler (lam $ \e1 ->
                      match e1 set_handler (lam $ \e2 ->
                        match e2 get_handler bye_handler))


-- include EVERYTHING !!!
class ( Symantics repr
      , SymSend   repr (Init,(Pid RSing,String))
      , SymRecv   repr (Init,(Pid RSing,String))
      , SymSend   repr (Set,String)
      , SymRecv   repr (Set,String)
      , SymSend   repr (Get,Pid RSing)
      , SymRecv   repr (Get,Pid RSing)
      , SymSend   repr Ok
      , SymRecv   repr Ok
      , SymSend   repr Bye
      , SymRecv   repr Bye
      , SymSend   repr String
      , SymRecv   repr String
      , SymRecv   repr Do_serve_t
      ) => ParikhSemantics repr
