{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return, id)
import Symmetry.Language
import Symmetry.Verify
import Data.Either
import SrcHelper
import Symmetry.SymbEx

type Msg = (Int, (Pid RSing, Int)) -- Cmd, K, V
                      -- Cmd=0 = Init
                      -- Cmd=1 = Get
                      -- Cmd=2 = Set V
                      -- Cmd=3 = Bye

expectMsg :: DSL repr => repr (Process repr Msg)
expectMsg = recv

server :: forall repr. DSL repr => repr (Process repr Int)
server = do m1 <- expectMsg
            match (proj1 m1 `eq` int 0)
                  (lam $ \_ -> do
                     send (proj1 (proj2 m1)) tt
                  )
                  (lam $ \_ -> die)
            int 0 |> fixM serveLoop
  where
    serveLoop :: repr ((Int -> Process repr Int) -> Int -> Process repr Int)
    serveLoop = lam $ \f -> lam $ \s ->
      do m <- expectMsg
         match (proj1 m `eq` int 0)
                 (lam $ \_ -> die)
                 (lam $ \_ ->
                    match (proj1 m `eq` int 1)
                            (lam $ \_ -> do
                               send (proj1 (proj2 m)) s
                               s |> f)
                            (lam $ \_ -> match (proj1 m `eq` int 2)
                                         (lam $ \_ -> s |> f)
                                         (lam $ \_ -> return s)))


client :: DSL repr => repr (Pid RSing -> Process repr ())
client = lam $ \server ->
  do me <- self
     send server (pair (int 0) (pair me (int 0)))
     _ :: repr () <- recv
     send server (pair (int 2) (pair me (int 0)))
     send server (pair (int 3) (pair me (int 0)))
     return tt

main :: IO ()
main = checkerMain (exec $ do r   <- newRSing
                              srv <- self
                              spawn r (srv |> client)
                              (server >> return tt))
