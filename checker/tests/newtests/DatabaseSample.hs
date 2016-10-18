{-# Language TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return, id, lookup)
import qualified Prelude as Pre ((>>=), (>>), fail, return, id, lookup)
import Symmetry.Language as L
import Symmetry.Verify
import Symmetry.SymbEx
import SrcHelper

type Database = Pid RSing
type Key      = Int
type Value    = Int
type NodeId   = Pid RSing

type MV = () :+: Value

type GetMsgT = (Key, Pid RSing)
type SetMsgT = (Key, Value)
type MsgT    = GetMsgT :+: SetMsgT

getMsg :: DSL repr => repr Key -> repr (Pid RSing) -> repr MsgT
getMsg k p = inl (pair k p)

setMsg :: DSL repr => repr Key -> repr Value -> repr MsgT
setMsg k v = inr (pair k v)

dbProc :: DSL repr => repr (Int -> Process repr ())
dbProc  = lam $ \workerCount -> do
  peers   <- newRMulti
  workers <- spawnMany peers workerCount worker
  app loop workers

loop :: DSL repr => repr (Pid RMulti -> Process repr ())
loop  = lam $ \workers ->
          do let loop_h = lam $ \arg ->
                            do req :: repr MsgT <- recv
                               let helper = lam $ \m -> lam $ \k ->
                                     do let w = L.lookup workers arb
                                        send w m
                               match req
                                 (lam $ \m -> app2 helper (inl m) (proj1 m))
                                 (lam $ \m -> app2 helper (inr m) (proj1 m))
                               return tt
             forever (app loop_h tt)

createDB :: DSL repr => repr (Int -> Process repr Database)
createDB  = lam $ \workerCount -> do
  r <- newRSing
  spawn r (workerCount |> dbProc)

set :: DSL repr => repr (Database -> Key -> Value -> Process repr ())
set  = lam $ \db -> lam $ \k -> lam $ \v -> send db (setMsg k v)

get :: DSL repr => repr (Database -> Key -> Process repr MV)
get  = lam $ \db -> lam $ \k ->
         do me <- self
            send db (getMsg k me)
            msg :: repr MV <- recv
            return msg

worker :: DSL repr => repr (Process repr ())
worker
  = do forever (app workerLoop nil)
       return tt
  where
    workerLoop
      = lam $ \map -> do
           msg :: repr MsgT <- recv
           match msg
             (lam $ \m ->
                do let (k, p) = (proj1 m, proj2 m)
                   result <- app2 SrcHelper.lookup k map
                   send p result
                   return map)
             (lam $ \m ->
                do let (k, v) = (proj1 m, proj2 m)
                   return (cons (pair k v) map))
           return tt

master :: DSL repr => repr (Int -> Process repr ())
master  = lam $ \workerCount -> do
  db <- workerCount |> createDB
  app3 set db (int 0) (int 10)
  return tt


main :: IO ()
main  =
  workerCount Pre.>>= \n ->
    checkerMain $ exec $ (int n) |> master
