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

type Request  = T "Req" (Pid RSing :+: (Pid RSing :+: Value))
type Response = T "Resp" (() :+: ())
type Value    = Int

mkAlloc :: DSL repr => repr (Pid RSing -> Request)
mkAlloc = lam $ \p -> lift (TyName :: TyName "Req") (inl p)

mkLookup :: DSL repr => repr (Pid RSing -> Request)
mkLookup = lam $ \p -> lift (TyName :: TyName "Req") (inr (inl p))

mkValue :: DSL repr => repr (Int -> Request)
mkValue = lam $ \p -> lift (TyName :: TyName "Req") (inr (inr p))

mkFree :: DSL repr => repr Response
mkFree = lift (TyName :: TyName "Resp") (inl tt)

mkAllocd :: DSL repr => repr Response
mkAllocd = lift (TyName :: TyName "Resp") (inr tt)

client :: DSL repr => repr (Pid RSing -> Process repr ())
client
  = lam $ \db -> do me  <- self
                    msg <- nondetVal (app mkAlloc me) (app mkLookup me)
                    send db msg
                    match (forget msg)
                      -- Did I alloc?
                      (lam $ \_ -> do resp :: repr Response <- recv
                                      let x = arb :: repr Int
                                      match (forget resp)
                                        (lam $ \_ -> return tt {- send db x -}) -- value
                                        (lam $ \_ -> return tt))
                      -- Did I Lookup?
                      (lam $ \_ -> do v :: repr Response <- recv
                                      return tt)
database :: DSL repr => repr (Process repr ())
database
  = app (fixM dbLoop) tt
  where
    dbLoop = lam $ \self -> lam $ \_ ->
                do msg :: repr Request <- recv
                   match (forget msg)
                           (lam $ \p -> do let b = arb :: repr Boolean
                                           match b
                                             (lam $ \_ -> do send p mkFree
                                                             -- v :: repr Value <- recv
                                                             return tt)
                                             (lam $ \_ -> do send p mkAllocd
                                                             return tt))
                           (lam $ \m' -> match m'
                                           (lam $ \p -> do let v = arb :: repr Value
                                                           send p v)
                                           (lam $ \_ -> die))
                   tt |> self

mainProc :: DSL repr => repr (Process repr ())
mainProc = do rcs <- newRMulti
              db  <- self
              cs  <- spawnMany rcs arb (db |> client)
              database

main :: IO ()
main = checkerMain (exec mainProc)
