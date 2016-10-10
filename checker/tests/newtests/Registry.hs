{-# Language RebindableSyntax    #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts    #-}
{-# Language DataKinds           #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

-- From TransDPOR

type MasterMsg = T "MasterMsg" (Pid RSing)
type ClientMsg = T "ClientMsg" (Pid RSing)

mkMaster :: DSL repr => repr (Pid RSing) -> repr MasterMsg
mkMaster = lift (TyName :: TyName "MasterMsg")

mkClient :: DSL repr => repr (Pid RSing) -> repr ClientMsg
mkClient = lift (TyName :: TyName "ClientMsg")

master :: DSL repr
       => repr (Pid RMulti -> Pid RSing -> Process repr ())
master = lam $ \clients -> lam $ \reg ->
  do me <- self

     -- Tell the registry about me
     send reg (mkMaster me)

     -- Tell the clients about the registry
     doMany "l1" clients $ lam $ \c ->
       send c (mkMaster reg)

     -- Barrier from registry
     recv

registry :: DSL repr
         => repr (Int -> Process repr ())
registry = lam $ \nClients ->
  do -- get master PID
     master :: repr MasterMsg <- recv

     -- Wait for clients
     doN "l2" nClients $ lam $ \_ ->
       do p :: repr ClientMsg <- recv
          return tt

     -- Tell master OK
     send (forget master) tt

client :: DSL repr
       => repr (Process repr ())
client =
  do me                         <- self
     registry :: repr MasterMsg <- recv
     send (forget registry) (mkClient me)

go :: DSL repr
     => repr (Int -> Process repr ())
go = lam $ \nClients ->
  do rRegistry <- newRSing
     rClients  <- newRMulti

     reg       <- spawn rRegistry (nClients |> registry)
     cs        <- spawnMany rClients nClients client
     (app (app master cs) reg)

main :: IO ()
main = checkerMain (exec (arb |> go))
