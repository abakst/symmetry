{-# Language TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return, id, lookup)
import Symmetry.Language as L
import Symmetry.Verify
import Symmetry.SymbEx
import SrcHelper

type Database = Pid RSing
type Key      = String
type Value    = String
type NodeId   = Pid RSing

type MV = () :+: Value

type GetMsgT = (Key, Pid RSing)
type SetMsgT = (Key, Value)
type MsgT    = GetMsgT :+: SetMsgT

getMsg :: DSL repr => repr Key -> repr (Pid RSing) -> repr MsgT
getMsg k p = inl (pair k p)

setMsg :: DSL repr => repr Key -> repr Value -> repr MsgT
setMsg k v = inr (pair k v)

dbProc :: DSL repr => repr (Process repr ())
dbProc  = do peers   <- newRMulti
             workers <- spawnMany peers (int workerCount) worker
             app loop workers

-- create the illusion of `ord` function
-- ord :: DSL repr => repr (String -> Int)
-- ord  = lam $ \s -> ifte (lt s (str "m"))
--                      (ifte (lt s (str "f")) (int 0) (int 1))
--                      (ifte (lt s (str "s")) (int 2) (int 3))

keyspace :: DSL repr => repr (Int -> [Int])
keyspace  = lam $ \n -> cons n (cons (plus n (int workerCount_div_2)) nil)

loop :: DSL repr => repr (Pid RMulti -> Process repr ())
loop  = lam $ \workers ->
          do let loop_h = lam $ \loop -> lam $ \arg ->
                            do req :: repr MsgT <- recv
                               let helper = lam $ \m -> lam $ \k ->
                                     -- matchList (app keyspace (app ord k))
                                     --   (lam $ \_  -> return tt)
                                     --   (lam $ \ht -> send (L.lookup workers (proj1 ht)) m)
                                     -- we really want a function that selects one of the
                                     -- workers, but just model that with arbitrary
                                     -- choice for now
                                     do let w = L.lookup workers arb
                                        send w m
                               match req
                                 (lam $ \m -> app2 helper (inl m) (proj1 m))
                                 (lam $ \m -> app2 helper (inr m) (proj1 m))
                               app loop arg
             app (fixM loop_h) tt

createDB :: DSL repr => repr (Process repr Database)
createDB  = do r <- newRSing
               spawn r dbProc

set :: DSL repr => repr (Database -> Key -> Value -> Process repr ())
set  = lam $ \db -> lam $ \k -> lam $ \v -> send db (setMsg k v)

get :: DSL repr => repr (Database -> Key -> Process repr MV)
get  = lam $ \db -> lam $ \k ->
         do me <- self
            send db (getMsg k me)
            msg :: repr MV <- recv
            return msg

worker :: DSL repr => repr (Process repr ())
worker  = do let worker_h = lam $ \worker -> lam $ \map ->
                              do msg :: repr MsgT <- recv
                                 match msg
                                   (lam $ \m ->
                                      do let k    = proj1 m
                                         let port = proj2 m
                                         res <- app2 SrcHelper.lookup k map
                                         send port res
                                         app worker map)
                                   (lam $ \m ->
                                      do let k = proj1 m
                                         let v = proj2 m
                                         app worker (cons (pair k v) map))
             app (fixM worker_h) nil
             return tt

master :: DSL repr => repr (Process repr ())
master  = do db <- createDB
             let words = cons (pair (str "key1") (str "val1")) $
                           cons (pair (str "key2") (str "val2"))
                             nil
             matchList words (lam $ \_  -> ret tt)
                             (lam $ \ht -> let x = proj1 ht
                                            in app3 set db (proj1 x) (proj2 x))
             matchList words (lam $ \_  -> ret tt)
                             (lam $ \ht -> do let k = proj1 $ proj1 ht
                                              r <- app2 get db k
                                              ret tt)
             forever $ return tt

workerCount       = 4
workerCount_div_2 = workerCount `div` 2

main :: IO ()
main  = checkerMain $ exec master
