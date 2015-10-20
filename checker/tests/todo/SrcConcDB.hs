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
      , SymSend   repr ALV
      , SymRecv   repr ALV
      , SymSend   repr LookupResT
      , SymRecv   repr LookupResT
      , SymSend   repr FreeAllocated
      , SymRecv   repr FreeAllocated
      , SymTypes  repr Int (Pid RSing)
      , SymTypes  repr (Int, Pid RSing) (LookupT :+: ValueT)
      , SymTypes  repr (Int, Pid RSing) ValueT
      , SymTypes  repr () ()
      , SymTypes  repr () Int
      , SymTypes  repr Int Int
      , SymMatch  repr () () Int
      , SymMatch  repr () () (Process ())
      , SymMatch  repr LookupT ValueT LookupT
      , SymMatch  repr AllocT (LookupT :+: ValueT) AllocT
      , SymMatch  repr () Int (Process ())
      , SymMatch  repr () () (() :+: Int)
      , SymMatch  repr AllocT (LookupT :+: ValueT) (Process ())
      , SymMatch  repr (Int, Pid RSing) ValueT (Process ())
      ) => CDBSem repr

--instance CDBSem SymbEx

concdb :: CDBSem repr => repr (Process ())
concdb  = do r  <- newRSing
             db <- spawn r (app database nil)
             app spawnmany (app client db)

spawnmany :: CDBSem repr => repr (Process () -> Process ())
spawnmany  = lam $ \f -> do r <- newRSing
                            spawn r f
                            b <- app any_bool tt
                            ifte b (app spawnmany f) (return tt)

database :: CDBSem repr => repr ([(Int,Int)] -> Process ())
database  = lam $ \l ->
              let allocHandler = lam $ \msg ->
                    let key = proj1 msg
                        p   = proj2 msg
                     in match (app2 lookup key l)
                          (lam $ \_ -> do send p free_msg
                                          val <- recv_value
                                          ifte (eq (proj2 val) p)
                                               (app database (cons (pair key (proj1 val)) l))
                                               fail)
                          (lam $ \x -> do send p allocated_msg
                                          app database l)
                  lookupHandler = lam $ \msg ->
                    let key = proj1 msg
                        p   = proj2 msg
                     in do send p (app2 lookup key l)
                           app database l
               in do msg :: repr ALV <- recv
                     match msg allocHandler $ lam $ \e1 ->
                       match e1 lookupHandler fail

client :: CDBSem repr => repr (Pid RSing -> Process ())
client  = lam $ \db ->
            do choice <- app any_bool tt
               me     <- self
               let insert_h = do k <- app any_nat tt
                                 send db (app2 alloc_msg k me)
                                 let free_h = lam $ \_ ->
                                       do v <- app any_nat tt
                                          send db (app2 value_msg v me)
                                          app client db
                                     alloc_h = lam $ \_ -> app client db
                                  in do msg :: repr FreeAllocated <- recv
                                        match msg free_h alloc_h
                   lookup_h = do k <- app any_nat tt
                                 send db (app2 lookup_msg k me)
                                 msg :: repr LookupResT <- recv
                                 match msg
                                   (lam $ \_ -> app client db)
                                   (lam $ \x -> app client db)
                in ifte choice insert_h lookup_h
