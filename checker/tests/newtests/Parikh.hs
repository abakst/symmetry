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

type Msg = (Pid RSing) :+:        -- Init
           ((Pid RSing) :+:       -- Get
            ((Pid RSing, Int) :+: -- Set V
             (Pid RSing)))        -- Bye

initMsg :: (DSL repr) => repr (Pid RSing -> Msg)
initMsg = lam $ \p -> inl p

setMsg :: (DSL repr) => repr (Pid RSing -> Int -> Msg)
setMsg = lam $ \p -> lam $ \n -> inr (inr (inl (pair p n)))

byeMsg :: (DSL repr) => repr (Pid RSing -> Msg)
byeMsg = lam $ \p -> inr (inr (inr p))

server :: forall repr. DSL repr => repr (Process repr Int)
server = do m1 :: repr Msg <- recv
            match m1
                  (lam $ \m -> send m tt) -- Init
                  (lam $ \_ -> die)
            int 0 |> fixM serveLoop
  where
    serveLoop :: repr ((Int -> Process repr Int) -> Int -> Process repr Int)
    serveLoop = lam $ \f -> lam $ \s ->
      do m :: repr Msg <- recv
         match m
           (lam $ \_ -> die) -- Init
           (lam $ \m' ->
               match m'
                 (lam $ \m -> do send m s -- Get
                                 s |> f)
                 (lam $ \m'' -> match m''
                                  (lam $ \_ -> s |> f)     -- Set
                                  (lam $ \_ -> return s))) -- Bye


client :: DSL repr => repr (Pid RSing -> Process repr ())
client = lam $ \server ->
  do me <- self
     send server (app initMsg me)
     _ :: repr () <- recv
     send server (app2 setMsg me (int 0))
     send server (app byeMsg me)
     return tt

main :: IO ()
main = checkerMain (exec $ do r   <- newRSing
                              srv <- self
                              spawn r (srv |> client)
                              (server >> return tt))
