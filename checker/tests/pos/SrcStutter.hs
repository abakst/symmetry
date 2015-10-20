{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify
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
b_msg = inr tt

stutter :: StutterSem repr => repr (Process ())
stutter  = do role <- newRSing
              p    <- spawn role (app my_sttr (lam $ \a -> app dosmt a))
              app sendAB p
              ret tt

dosmt :: StutterSem repr => repr (Msg -> Process ())
dosmt  = lam $ \msg -> match msg fail (lam $ \_ -> ret tt)

sendAB :: StutterSem repr => repr ((Pid RSing) -> Process (Pid RSing))
sendAB  = let fix_f = lam $ \f -> lam $ \pid -> do send pid a_msg
                                                   send pid b_msg
                                                   app f pid
           in lam $ \pid -> app (fixM fix_f) pid

-- sendA :: StutterSem repr => repr ((Pid RSing) -> Process ())
-- sendA  = lam $ \pid -> do send pid a_msg
--                           app sendB pid

-- sendB :: StutterSem repr => repr ((Pid RSing) -> Process ())
-- sendB = lam $ \pid -> do send pid b_msg
--                          app sendA pid

my_sttr :: StutterSem repr => repr ((Msg->Process())->Process())
my_sttr  = let fix_sttr = lam $ \sttr -> lam $ \f ->
                 do msg1 :: repr Msg <- recv
                    msg2 :: repr Msg <- recv
                    app f msg2
                    app sttr f
            in lam $ \f -> do app (fixM fix_sttr) f
                              ret tt

-- sttr :: StutterSem repr => repr ((Msg->Process())->Process())
-- sttr  = lam $ \f -> do msg :: repr Msg <- recv
--                        app unsttr f

-- unsttr :: StutterSem repr => repr ((Msg->Process())->Process())
-- unsttr  = lam $ \f -> do msg :: repr Msg <- recv
--                          app f msg
--                          app sttr f


main :: IO ()
main  = checkerMain $ exec stutter
