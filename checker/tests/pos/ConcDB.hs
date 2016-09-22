{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return, id, lookup)
import Symmetry.Language
import Symmetry.Verify
import Symmetry.SymbEx
import SrcHelper

-- msg1 : Alloc, Lookup
-- msg2 : Value
-- msg3 : Free, Allocated

type AllocT  = (Int,Pid RSing)
type LookupT = (Int,Pid RSing)
type ValueT  = (Int,Pid RSing)

type ALV = AllocT :+: (LookupT :+: ValueT)

type FreeAllocated = () :+: -- Free
                     ()     -- Allocated

type LookupResT = () :+: Int

alloc_msg :: CDBSem repr => repr (Int -> Pid RSing -> ALV)
alloc_msg  = lam $ \n -> lam $ \pid -> inl $ pair n pid

lookup_msg :: CDBSem repr => repr (Int -> Pid RSing -> ALV)
lookup_msg  = lam $ \n -> lam $ \pid -> inr $ inl $ pair n pid

value_msg :: CDBSem repr => repr (Int -> Pid RSing -> ALV)
value_msg  = lam $ \n -> lam $ \pid -> inr $ inr $ pair n pid

free_msg :: CDBSem repr => repr (FreeAllocated)
free_msg  = inl tt

allocated_msg :: CDBSem repr => repr (FreeAllocated)
allocated_msg  = inr tt

recv_alloc :: CDBSem repr => repr (Process repr AllocT)
recv_alloc  = do msg :: repr ALV <- recv
                 match msg id reject

recv_lookup :: CDBSem repr => repr (Process repr LookupT)
recv_lookup  = do msg :: repr ALV <- recv
                  match msg reject $ lam $ \e1 ->
                    match e1 id reject

recv_value :: CDBSem repr => repr (Process repr ValueT)
recv_value  = do msg :: repr ALV <- recv
                 match msg reject $ lam $ \e1 ->
                    match e1 reject id

class DSL repr => CDBSem repr

instance CDBSem SymbEx

concdb :: CDBSem repr => repr (Process repr ())
concdb  = do r  <- newRSing
             db <- spawn r (app database nil)
             rs <- newRMulti
             spawnMany rs arb (app client db)
             return tt

type T_db = [(Int,Int)]

f_database :: CDBSem repr
           => repr ((T_db -> Process repr T_db) -> T_db -> Process repr T_db)
f_database  = lam $ \database -> lam $ \l ->
                do let allocHandler = lam $ \msg ->
                         do let key = proj1 msg
                                p   = proj2 msg
                            lookup_res <- app2 SrcHelper.lookup key l
                            match lookup_res
                              (lam $ \_ -> do send p free_msg
                                              val <- recv_value
                                              ifte (eq (proj2 val) p)
                                                   (app database (cons (pair key (proj1 val)) l))
                                                   fail)
                              (lam $ \x -> do send p allocated_msg
                                              app database l)
                   let lookupHandler = lam $ \msg ->
                         do let key = proj1 msg
                                p   = proj2 msg
                            lookup_res <- app2 SrcHelper.lookup key l
                            send p lookup_res
                            app database l
                   msg :: repr ALV <- recv
                   match msg allocHandler $ lam $ \e1 ->
                     match e1 lookupHandler reject

database :: CDBSem repr => repr ([(Int,Int)] -> Process repr ())
database  = lam $ \l ->
              do app (fixM f_database) l
                 ret tt

f_client :: CDBSem repr
         => repr ((Pid RSing -> Process repr (Pid RSing)) -> Pid RSing -> Process repr (Pid RSing))
f_client  = lam $ \client -> lam $ \db ->
              do me     <- self
                 let insert_h = do send db (app2 alloc_msg arb me)
                                   let free_h = lam $ \_ ->
                                                  do send db (app2 value_msg arb me)
                                                     app client db
                                       alloc_h = lam $ \_ -> app client db
                                   msg :: repr FreeAllocated <- recv
                                   match msg free_h alloc_h
                     lookup_h = do send db (app2 lookup_msg arb me)
                                   msg :: repr LookupResT <- recv
                                   match msg
                                     (lam $ \_ -> app client db)
                                     (lam $ \x -> app client db)
                 ifte arb insert_h lookup_h

client :: CDBSem repr => repr (Pid RSing -> Process repr ())
client  = lam $ \db -> do app (fixM f_client) db
                          ret tt

main :: IO ()
main  = checkerMain $ exec concdb
