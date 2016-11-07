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

-- ##############################################################################
-- Message types and constructors
-- ##############################################################################

type Key   = String
type Value = Int
type KVS   = [(Key, Value)]

type LockRequest    = T "LockReq"    (Pid RSing)             -- lock request
type OwnerRequest   = T "OwnerReq"   (Pid RSing, () :+: Key) -- unlock or get request
type LockedResponse = T "LockedResp" ()                      -- locked acknowledgement
type ValResponse    = T "Resp"       Value                   -- query response

lockReq :: DSL repr => repr (Pid RSing -> LockRequest)
lockReq = lam $ \pid -> lift (TyName :: TyName "LockReq") pid

unlockReq :: DSL repr => repr (Pid RSing -> OwnerRequest)
unlockReq = lam $ \pid -> lift (TyName :: TyName "OwnerReq") (pair pid (inl tt))

getReq :: DSL repr => repr (Pid RSing -> Key -> OwnerRequest)
getReq = lam $ \pid -> lam $ \key ->
  lift (TyName :: TyName "OwnerReq") (pair pid (inr key))

ackResp :: DSL repr => repr LockedResponse
ackResp = lift (TyName :: TyName "LockedResp") tt

valResp :: DSL repr => repr (Value -> ValResponse)
valResp = lam $ \v -> lift (TyName :: TyName "Resp") v

-- ##############################################################################
-- Process descriptions
-- ##############################################################################

database :: DSL repr => repr (Process repr ())
database = do app (fixM database') (bool (Right ()))
              return tt
  where
    database' = lam $ \fix -> lam $ \isLocked -> do
      match isLocked
        -- db is locked
        (lam $ \_ -> do
            (req :: repr OwnerRequest) <- recv
            let req' = forget req
                pid  = proj1 req'
            match (proj2 req')
              (lam $ \_ -> (bool (Right ())) |> fix)          -- respond to unlock request
              (lam $ \key -> do send pid ((int 0) |> valResp) -- respond to get request
                                isLocked |> fix
              )
        )
        -- db is unlocked
        (lam $ \_ -> do
            (req :: repr LockRequest) <- recv -- get lock request
            let pid = forget req
            send pid ackResp        -- send acknowledgement
            (bool (Left ())) |> fix -- lock db
        )

client :: DSL repr => repr (Pid RSing -> Process repr ())      
client = lam $ \dbPid -> do
  me <- self
  send dbPid (me |> lockReq)                                 -- lock the server
  (_ :: repr LockedResponse) <- recv
  send dbPid $ (str "foobar") |> (me |> getReq)              -- get key
  (_ :: repr ValResponse) <- recv
  send dbPid (me |> unlockReq)                               -- unlock
  return tt

-- ##############################################################################
-- Init
-- ##############################################################################

mainProc :: DSL repr => repr (Process repr ())
mainProc = do dbPid <- self
              rcs   <- newRMulti
              cs    <- spawnMany rcs arb (dbPid |> client)
              database

main :: IO ()
main = checkerMain (exec mainProc)
