{-# Language RebindableSyntax    #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts    #-}
{-# Language DataKinds           #-}
{-# Language TypeOperators #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

-- From TransDPOR

-- type Msg = (Pid RSing) :+: (Pid RSing)

type MasterMsg = (Pid RSing) :+: ()
type ClientMsg = () :+: (Pid RSing)

mkMaster :: DSL repr => repr (Pid RSing) -> repr MasterMsg
mkMaster p = inl p

mkClient :: DSL repr => repr (Pid RSing) -> repr ClientMsg
mkClient p = inr p

master :: DSL repr
       => repr (Pid RMulti -> Pid RSing -> Process repr ())
master = lam $ \clients -> lam $ \reg ->
  do me <- self

     -- Tell the registry about me
     send reg (mkMaster me)

     -- Tell the clients about the registry
     doMany clients $ lam $ \c ->
       send c (mkMaster reg)

     -- Barrier from registry
     recv

registry :: DSL repr
         => repr (Int -> Process repr ())
registry = lam $ \nClients ->
  do -- get master PID
     master :: repr MasterMsg <- recv

     -- Wait for clients
     doN nClients $ lam $ \_ ->
       do p :: repr ClientMsg <- recv
          match p (lam $ \_ -> die)
                  (lam $ \_ -> return tt)

     -- Tell master OK
     match master (lam $ \m -> send m tt)
                  (lam $ \_ -> die)

client :: DSL repr
       => repr (Process repr ())
client =
  do me                         <- self
     registry :: repr MasterMsg <- recv
     match registry (lam $ \m -> send m (mkClient me))
                    (lam $ \_ -> die)

go :: DSL repr
     => repr (Int -> Process repr ())
go = lam $ \nClients ->
  do rRegistry <- newRSing
     rClients  <- newRMulti

     reg       <- spawn rRegistry (nClients |> registry)
     cs        <- spawnMany rClients nClients client
     (app (app master cs) reg)

clientCount = int 3

main :: IO ()
main = checkerMain (exec (clientCount |> go))
