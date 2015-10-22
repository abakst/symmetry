{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify
import Data.Either
import Symmetry.SymbEx

class ( Symantics repr
      , ArbPat repr ()
      , ArbPat repr (Pid RSing)
      ) => StutterSem repr

instance StutterSem SymbEx

type MsgA = () -- 1
type MsgB = () :+: () -- 2

aMsg :: StutterSem repr => repr MsgA
aMsg = tt

bMsg :: StutterSem repr => repr MsgB
bMsg = inr tt

stutter :: StutterSem repr => repr (Process repr ())
stutter  = do role <- newRSing
              p    <- spawn role sttr
              app sendAB p
              ret tt
         
sendAB :: StutterSem repr => repr (Pid RSing -> Process repr ())
sendAB  = lam $ \pid ->
            tt |> fixM (lam $ \loop -> lam $ \_  ->
                                       do send pid aMsg
                                          send pid bMsg
                                          tt |> loop)


sttr :: StutterSem repr => repr (Process repr ())
sttr  = tt |> fixM loop
  where
    loop = lam $ \fix_sttr -> lam $ \_ ->
              do _ :: repr MsgA <- recv
                 _ :: repr MsgB <- recv
                 app fix_sttr tt


main :: IO ()
main  = checkerMain $ exec stutter
