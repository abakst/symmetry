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
              p    <- spawn role (app sttr (lam $ \a -> app dosmt a))
              app sendAB p
              ret tt

--if msg = 'a'
--   then fail
--   else ()
dosmt :: StutterSem repr => repr (Msg -> Process ())
dosmt  = lam $ \msg -> match msg (lam $ \_ -> ret tt) fail

-- send the infinite sequence of ['a','b','a','b',...] messages
sendAB :: StutterSem repr => repr ((Pid RSing) -> Process (Pid RSing))
sendAB  = let fix_f = lam $ \f -> lam $ \pid -> do send pid a_msg
                                                   send pid b_msg
                                                   app f pid
           in lam $ \pid -> app (fixM fix_f) pid

-- get 2 messages, call dosmt on the second one, repeat
sttr :: StutterSem repr => repr ((Msg->Process())->Process())
sttr  = let helper = lam $ \fix_sttr -> lam $ \f ->
                 do msg1 :: repr Msg <- recv
                    msg2 :: repr Msg <- recv
                    app f msg2
                    app fix_sttr f
         in lam $ \f -> do app (fixM helper) f
                           ret tt


main :: IO ()
main  = checkerMain $ exec stutter
