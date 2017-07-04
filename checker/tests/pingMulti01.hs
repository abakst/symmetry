{-# Language RebindableSyntax #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module PingMulti00 where

import Prelude hiding ((>>=), (>>), fail, return) 
import Symmetry.Language.AST  
import Symmetry.Language.Syntax  
import Symmetry.SymbEx
import qualified Symmetry.IL.AST as IL
import Symmetry.IL.Render

type Message = Pid RSing :+: Pid RSing

app2 :: Symantics repr => repr (a -> b -> c) -> repr a -> repr b -> repr c
app2 f x y = f `app` x `app` y

main :: forall repr.
        (Symantics repr,
         SymSend repr (Pid RSing :+: Pid RSing),
         SymRecv repr (Pid RSing :+: Pid RSing),
         SymMatch repr (Pid RSing) (Pid RSing) (Process ()),
         SymTypes repr (Pid RSing) (Pid RSing))
     => repr (Int -> ())
main = lam $ \n -> exec $ do r <- newRMulti
                             app2 master r n
  where master = lam $ \r ->
                 lam $ \n ->
                    do ps <- spawnMany r n pingServer
                       myPid <- self
                       doMany ps (lam $ \p -> send p (ping myPid))
                       doMany ps (lam $ \_ -> do _ <- recv :: repr (Process Message)
                                                 ret tt)
                       ret tt
        pingServer = do myPid <- self
                        p     <- recv :: repr (Process Message)
                        match p
                          (lam $ \pid -> send pid (ping myPid))
                          (lam $ \_   -> ret tt)

        ping :: repr (Pid RSing) -> repr Message
        ping = inl

        pong :: repr (Pid RSing) -> repr Message
        pong = inr
