{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
{-# Language DataKinds #-}
module Main where

import Prelude hiding ((>>=), (>>), fail, return, id, lookup)
import Symmetry.Language
import Symmetry.Verify
import Symmetry.SymbEx


type Req      = (Int, (Pid RSing, Value))
type Request  = T "Req" Req
type Response = T "Resp" (() :+: ())
type Value    = Int

mkAlloc :: DSL repr => repr (Pid RSing -> Request)
mkAlloc = lam $ \p -> lift (TyName :: TyName "Req") (pair (int 0) (pair p (int 0)))

mkValue :: DSL repr => repr (Pid RSing -> Int -> Request)
mkValue = lam $ \p -> lam $ \v ->
          lift (TyName :: TyName "Req") (pair (int 1) (pair p v))

mkLookup :: DSL repr => repr (Pid RSing -> Value -> Request)
mkLookup = lam $ \p -> lam $ \k ->
           lift (TyName :: TyName "Req") (pair (int 2) (pair p k))

mkFree :: DSL repr => repr Response
mkFree = lift (TyName :: TyName "Resp") (inl tt)

mkAllocd :: DSL repr => repr Response
mkAllocd = lift (TyName :: TyName "Resp") (inr tt)

client :: DSL repr => repr (Pid RSing -> Process repr ())
client
  = lam $ \db -> do me  <- self
                    msg <- nondetVal (app mkAlloc me) (app (app mkLookup me) arb)
                    send db msg
                    match (proj1 (forget msg) `eq` int 0)
                      -- Did I alloc?
                      (lam $ \_ -> do resp :: repr Response <- recv
                                      let x = arb :: repr Int
                                      match (forget resp)
                                        (lam $ \_ -> return tt {- send db x -}) -- value
                                        (lam $ \_ -> return tt))
                      -- Did I Lookup?
                      (lam $ \_ -> do v :: repr Response <- recv
                                      return tt)
database :: forall repr. DSL repr => repr (Process repr ())
database
  = app (fixM dbLoop) tt
  where
    dbLoop = lam $ \self -> lam $ \_ ->
                do msg :: repr Request <- recv
                   let m = forget msg
                       p = proj1 (proj2 m)
                   match (proj1 m `eq` int 0)
                           (lam $ \_ ->
                              do let b = arb :: repr Boolean
                                 match b
                                  (lam $ \_ -> do send p mkFree
                                   -- v :: repr Value <- recv
                                                  return tt)
                                  (lam $ \_ -> do send p mkAllocd
                                                  return tt))
                           (lam $ \_ -> do let v = arb :: repr Value
                                           send p v)
                   tt |> self

mainProc :: DSL repr => repr (Process repr ())
mainProc = do rcs <- newRMulti
              db  <- self
              cs  <- spawnMany rcs arb (db |> client)
              database

main :: IO ()
main = checkerMain (exec mainProc)
