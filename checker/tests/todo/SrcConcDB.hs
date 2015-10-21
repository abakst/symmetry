{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcConcDB where

import Prelude (($), undefined, String, Int, fromInteger, negate)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import Data.Either
import SrcHelper
import Symmetry.SymbEx

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

recv_alloc :: CDBSem repr => repr (Process AllocT)
recv_alloc  = do msg :: repr ALV <- recv
                 return $ match msg id fail

recv_lookup :: CDBSem repr => repr (Process LookupT)
recv_lookup  = do msg :: repr ALV <- recv
                  return $ match msg fail $ lam $ \e1 ->
                             match e1 id fail

recv_value :: CDBSem repr => repr (Process ValueT)
recv_value  = do msg :: repr ALV <- recv
                 return $ match msg fail $ lam $ \e1 ->
                            match e1 fail id

class ( Symantics repr
      , SymSend repr ALV
      , SymRecv repr ALV
      , SymSend repr LookupResT
      , SymRecv repr LookupResT
      , SymSend repr FreeAllocated
      , SymRecv repr FreeAllocated
      , SymMatch repr () () (() :+: Int)
      , SymMatch repr () () (Process ())
      , SymMatch repr () () (Process (Process ()))
      , SymMatch repr () () (Process T_db)
      , SymMatch repr () () Int
      , SymMatch repr () Int (Process ())
      , SymMatch repr () Int (Process T_db)
      , SymMatch repr (Int, Pid RSing) ValueT (Process ())
      , SymMatch repr (Int, Pid RSing) ValueT (Process T_db)
      , SymMatch repr AllocT (LookupT :+: ValueT) (Process ())
      , SymMatch repr AllocT (LookupT :+: ValueT) (Process T_db)
      , SymMatch repr AllocT (LookupT :+: ValueT) AllocT
      , SymMatch repr LookupT ValueT LookupT
      , SymTypes repr () ()
      , SymTypes repr () Int
      , SymTypes repr (Int, Pid RSing) (LookupT :+: ValueT)
      , SymTypes repr (Int, Pid RSing) ValueT
      , SymTypes repr Int (Pid RSing)
      , SymTypes repr Int Int
      , SymMatch repr () () (Process (Pid RSing))
      , SymMatch repr () Int (Process (Pid RSing))
      ) => CDBSem repr

instance CDBSem SymbEx

concdb :: CDBSem repr => repr (Process ())
concdb  = do r  <- newRSing
             db <- spawn r (app database nil)
             app spawnmany (app client db)

spawnmany :: CDBSem repr => repr (Process () -> Process ())
spawnmany  = lam $ \f ->
               do let fix_sm = lam $ \spawnmany -> lam $ \f ->
                                 do r <- newRSing
                                    spawn r f
                                    b <- app any_bool tt
                                    ifte b (app spawnmany f) (ret f)
                  app (fixM fix_sm) f
                  ret tt

type T_db = [(Int,Int)]

f_database :: CDBSem repr
           => repr ((T_db -> Process T_db) -> T_db -> Process T_db)
f_database  = lam $ \database -> lam $ \l ->
                do let allocHandler = lam $ \msg ->
                         do let key = proj1 msg
                                p   = proj2 msg
                            match (app2 lookup key l)
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
                            send p (app2 lookup key l)
                            app database l
                   msg :: repr ALV <- recv
                   match msg allocHandler $ lam $ \e1 ->
                     match e1 lookupHandler fail

database :: CDBSem repr => repr ([(Int,Int)] -> Process ())
database  = lam $ \l ->
              do app (fixM f_database) l
                 ret tt

f_client :: CDBSem repr
         => repr ((Pid RSing -> Process (Pid RSing)) -> Pid RSing -> Process (Pid RSing))
f_client  = lam $ \client -> lam $ \db ->
              do choice <- app any_bool tt
                 me     <- self
                 let insert_h = do k <- app any_nat tt
                                   send db (app2 alloc_msg k me)
                                   let free_h = lam $ \_ ->
                                                  do v <- app any_nat tt
                                                     send db (app2 value_msg v me)
                                                     app client db
                                       alloc_h = lam $ \_ -> app client db
                                   msg :: repr FreeAllocated <- recv
                                   match msg free_h alloc_h
                     lookup_h = do k <- app any_nat tt
                                   send db (app2 lookup_msg k me)
                                   msg :: repr LookupResT <- recv
                                   match msg
                                     (lam $ \_ -> app client db)
                                     (lam $ \x -> app client db)
                 ifte choice insert_h lookup_h

client :: CDBSem repr => repr (Pid RSing -> Process ())
client  = lam $ \db -> do app (fixM f_client) db
                          ret tt
