{-# Language RebindableSyntax #-}
{-# Language TypeOperators #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return) 
import Symmetry.Language
import Symmetry.Verify

proxy :: forall r. DSL r
           => r (Pid RMulti -> Process r ())
proxy = lam $ \ps ->
        forever $ do doMany ps (lam $ \p -> send p tt)
                     return tt

chatServer :: forall r. DSL r
           => r (Process r ())
chatServer = do r  <- newRSing
                ps <- recv
                spawn r (app proxy ps)
                forever $ recv
-- 1. spawn a proxy that will send
-- 2. loop forever receiving messages

master :: forall r. DSL r
       => r (Int -> Process r ())
master = lam $ \n -> do chatRole <- newRMulti
                        ps <- spawnMany chatRole n chatServer
                        doMany ps (lam $ \p -> send p ps)
                        return tt
         -- 1. Spawn a bunch of clients
         -- 3. Send the "bunch" of clients to each client
main = checkerMain (exec (app master arb))
