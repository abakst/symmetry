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

dbProc :: DSL repr => repr (Process repr ())
dbProc  = do peers   <- newRMulti
             workers <- spawnMany peers workerCount worker
             app loop workers

-- create the illusion of `ord` function
-- ord :: DSL repr => repr (String -> Int)
-- ord  = lam $ \s -> ifte (lt s (str "m"))
--                      (ifte (lt s (str "f")) (int 0) (int 1))
--                      (ifte (lt s (str "s")) (int 2) (int 3))

keyspace :: DSL repr => repr (Int -> [Int])
keyspace  = lam $ \n -> cons n (cons (plus n workerCount_div_2) nil)

loop :: DSL repr => repr (Pid RMulti -> Process repr ())
loop  = lam $ \workers ->
          do let loop_h = lam $ \arg ->
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
                               return tt
             forever loop_h tt

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
worker
  = do forever workerLoop nil
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

master :: DSL repr => repr (Process repr ())
master  = do db <- createDB
             -- let words = cons (pair (int 0) (int 10)) $
             --               cons (pair (int 1) (int 20))
             --                 nil
             -- matchList words (lam $ \_  -> ret tt)
             --                 (lam $ \ht -> let x = proj1 ht
             --                                in app3 set db (proj1 x) (proj2 x))
             -- matchList words (lam $ \_  -> ret tt)
             --                 (lam $ \ht -> do let k = proj1 $ proj1 ht
             --                                  r <- app2 get db k
             --                                  ret tt)
             app3 set db (int 0) (int 10)
             return tt

workerCount       :: DSL repr => repr Int
workerCount       = arb
workerCount_div_2 :: DSL repr => repr Int
workerCount_div_2 = arb

main :: IO ()
main  = checkerMain $ exec master
