{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcStutter where

import Prelude (($), undefined, Int, fromInteger)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import GHC.Num ((+))
import Data.Either
import Symmetry.SymbEx

class ( Symantics repr
      , SymSend   repr Msg
      , SymRecv   repr Msg
      , SymMatch repr () () (Process ())
      , SymTypes repr () ()
      ) => StutterSem repr

instance StutterSem SymbEx

type Msg = () :+: ()

a_msg :: StutterSem repr => repr Msg
a_msg = inl tt

b_msg :: StutterSem repr => repr Msg
b_msg = inl tt

stutter :: StutterSem repr => repr (Process ())
stutter  = do role <- newRSing
              p    <- spawn role (app sttr (lam $ \a -> app dosmt a))
              app sendA p

dosmt :: StutterSem repr => repr (Msg -> Process ())
dosmt  = lam $ \msg -> match msg fail (lam $ \_ -> ret tt)

sendA :: StutterSem repr => repr ((Pid RSing) -> Process ())
sendA  = lam $ \pid -> do send pid a_msg
                          app sendB pid

sendB :: StutterSem repr => repr ((Pid RSing) -> Process ())
sendB = lam $ \pid -> do send pid b_msg
                         app sendA pid

sttr :: StutterSem repr => repr ((Msg->Process())->Process())
sttr  = lam $ \f -> do msg :: repr Msg <- recv
                       app unsttr f

unsttr :: StutterSem repr => repr ((Msg->Process())->Process())
unsttr  = lam $ \f -> do msg :: repr Msg <- recv
                         app f msg
                         app sttr f

