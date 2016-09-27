{-# Language RebindableSyntax    #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts    #-}
{-# Language DataKinds           #-}
{-# Language TypeOperators       #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

type ClientReq_ = (Pid RSing) :+: (Pid RSing)

type ClientReq  = T "ClientReq" ClientReq_
type ForwardMsg = T "Forward" ClientReq_
type FWResponse = T "FWInt" Int

mkFWResponse :: DSL repr => repr Int -> repr FWResponse
mkFWResponse = lift (TyName :: TyName "FWInt")

mkReqGood :: DSL repr => repr (Pid RSing) -> repr ClientReq
mkReqGood p = lift (TyName :: TyName "ClientReq") (inl p)

mkForward :: DSL repr => repr ClientReq_ -> repr ForwardMsg
mkForward = lift (TyName :: TyName "Forward")

server :: DSL repr => repr (Process repr ())
server =
  do msg :: repr ForwardMsg <- recv
     match (forget msg)
       (lam $ \p -> send p (int 0))
       (lam $ \_ -> die)

firewall :: DSL repr
         => repr (Pid RSing -> Process repr ())
firewall = lam $ \server ->
  do msg :: repr ClientReq <- recv
     me <- self
     match (forget msg)
       (lam $ \p -> do send server (mkForward (inl me))
                       x :: repr Int <- recv
                       send p x)
       (lam $ \p -> send p (int (-1)))

client :: DSL repr
       => repr (Pid RSing -> Process repr ())
client = lam $ \fw ->
  do me <- self
     send fw (mkReqGood me)
     _ :: repr FWResponse <- recv
     return tt

master :: DSL repr => repr (Process repr ())
master = do rsrv <- newRSing
            rfw  <- newRSing
            rcl  <- newRSing

            srv  <- spawn rsrv server
            fw   <- spawn rfw (app firewall srv)
            c    <- spawn rcl (app client fw)

            return tt

main :: IO ()
main = checkerMain (exec master)
