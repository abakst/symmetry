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

pingServer :: (DSL repr) => repr (Process repr ())
pingServer = do (_ :: repr ()) <- recv -- 'recv a tt'
                return tt

master :: (DSL repr) => repr (RMulti -> Int -> Process repr ())
master = lam $ \r -> lam $ \n ->
   do ps <- spawnMany r n pingServer
      doMany ps (body n)
      sent <- msgsSent
      app assert (sent `eq` n)
      return tt
  where
    body n = lam $ \p -> do sent <- msgsSent
                            app assert (sent `lt` n)
                            send p tt

msgsSent :: DSL repr => repr (Process repr Int)
msgsSent = undefined                                 

assert :: DSL repr => repr (Boolean -> Process repr ())            
assert = undefined

mainProc :: (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 app (app master r) n

main :: IO ()
main = checkerMain (arb |> mainProc)
