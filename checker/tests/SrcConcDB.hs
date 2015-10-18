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

-- msg1 : Alloc, Lookup
-- msg2 : Value
-- msg3 : Free, Allocated

type AllocT  = (Int,Pid RSing)
type LookupT = (Int,Pid RSing)
type ValueT  = (Int,Pid RSing)

type ALV = AllocT :+: (LookupT :+: ValueT)

type FreeAllocated = () :+: -- Free
                     ()     -- Allocated

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
      , SymSend   repr FreeAllocated
      , SymRecv   repr FreeAllocated
      ) => CDBSem repr

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
                     in match (lookup key l)
                          (do send p free_msg
                              val <- recv_val
                              if (eq (proj2 val) p)
                                 then app database (cons (pair key (proj1 val)) l)
                                 else fail)
                          (lam $ \x -> do send p allocated_msg
                                          app database l)
                  lookupHandler = lam $ \msg ->
                    let key = proj1 msg
                        p   = proj2 msg
                     in do send p (lookup)
                           undefined
              undefined

client   = undefined
