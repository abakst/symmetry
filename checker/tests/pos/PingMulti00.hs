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

fooDSL :: DSL repr => repr (a -> b -> c -> d)
fooDSL = lam $ \x -> lam $ \y -> lam $ \z ->
           undefined

type Message repr = repr (Pid RSing :+: Pid RSing)
ping :: (DSL repr) => repr (Pid RSing) -> Message repr
ping = inl

pong :: (DSL repr) => repr (Pid RSing) -> Message repr
pong = inr

pingServer :: (DSL repr) => repr (Process repr ())
pingServer = do myPid <- self
                p     <- recv
                match p
                  (lam $ \pid -> send pid (ping myPid))
                  (lam $ \(_ :: repr (Pid RSing))   -> die)

master :: (DSL repr) => repr (RMulti -> Int -> Process repr ())
master = lam $ \r -> lam $ \n ->
   do ps <- spawnMany r n pingServer
      myPid <- self
      doMany ps (lam $ \p -> send p (ping myPid))
      doMany ps (lam $ \_ -> do (_ :: Message repr)  <- recv
                                ret tt)

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 app (app master r) n

main :: IO ()
main = checkerMain (int 10 |> mainProc)
