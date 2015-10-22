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
      , ArbPat repr ()
      , ArbPat repr (Pid RSing)
      ) => StutterSem repr

instance StutterSem SymbEx

type MsgA = () -- 1
type MsgB = () :+: () -- 2

a_msg :: StutterSem repr => repr MsgA
a_msg = tt

b_msg :: StutterSem repr => repr MsgB
b_msg = inr tt

stutter :: StutterSem repr => repr (Process repr ())
stutter  = do role <- newRSing
              p    <- spawn role sttr
              app sendAB p
              ret tt
         
-- send the infinite sequence of ['a','b','a','b',...] messages
sendAB :: StutterSem repr => repr (Pid RSing -> Process repr ())
sendAB  = lam $ \pid ->
            tt |> fixM (lam $ \loop -> lam $ \_  ->
                                       do send pid a_msg
                                          send pid b_msg
                                          tt |> loop)


  -- let fix_f = lam $ \f -> lam $ \pid -> do send pid a_msg
  --                                                  send pid a_msg
  --                                                  app f pid
  --          in lam $ \pid -> app (fixM fix_f) pid

-- get 2 messages, call dosmt on the second one, repeat
sttr :: StutterSem repr => repr (Process repr ())
sttr  = tt |> fixM loop
  where
    loop = lam $ \fix_sttr -> lam $ \_ ->
              do _ :: repr MsgA <- recv
                 _ :: repr MsgB <- recv
                 app fix_sttr tt


main :: IO ()
main  = checkerMain $ exec stutter
