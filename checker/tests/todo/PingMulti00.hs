{-# Language RebindableSyntax #-}
{-# Language TypeOperators #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module PingMulti00 where

import Prelude hiding ((>>=), (>>), fail, return) 
import Symmetry.Language
import Symmetry.Verify
-- import qualified Symmetry.IL.AST as IL
-- import Symmetry.IL.Render

type Message repr = repr (Pid RSing :+: Pid RSing)
ping :: (SymTypes repr (Pid RSing) (Pid RSing), Symantics repr) =>
        repr (Pid RSing) -> Message repr
ping = inl

pong :: (SymTypes repr (Pid RSing) (Pid RSing), Symantics repr) =>
        repr (Pid RSing) -> Message repr
pong = inr

pingServer :: (SymTypes repr (Pid RSing) (Pid RSing),
               SymMatch repr (Pid RSing) (Pid RSing) (Process ()),
               SymSend repr (Pid RSing :+: Pid RSing),
               SymRecv repr (Pid RSing :+: Pid RSing),
                       Symantics repr)
           => repr (Process ())
pingServer = do myPid <- self
                p     <- recv
                match p
                  (lam $ \pid -> send pid (ping myPid))
                  (lam $ \(_ :: repr (Pid RSing))   -> ret tt)

master :: (Symantics repr, SymSend repr (Pid RSing :+: Pid RSing), SymRecv repr (Pid RSing :+: Pid RSing),
               SymMatch repr (Pid RSing) (Pid RSing) (Process ()),
                     SymTypes repr (Pid RSing) (Pid RSing))
       => repr (RMulti -> Int -> Process ())
master = lam $ \r -> lam $ \n ->
   do ps <- spawnMany r n pingServer
      myPid <- self
      doMany ps (lam $ \p -> send p (ping myPid))
      doMany ps (lam $ \_ -> do (_ :: Message repr)  <- recv
                                ret tt)
      ret tt

mainProc :: (Symantics repr, SymSend repr (Pid RSing :+: Pid RSing), SymRecv repr (Pid RSing :+: Pid RSing),
               SymMatch repr (Pid RSing) (Pid RSing) (Process ()),
                     SymTypes repr (Pid RSing) (Pid RSing))
     => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 app (app master r) n

main :: IO ()
main = checkerMain (repI 10 |> mainProc)
