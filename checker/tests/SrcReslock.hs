{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcReslock where

import Prelude (($), undefined, String, Int, fromInteger, negate)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import Data.Either
import SrcHelper

type Cmd = Int :+: ()            -- Write Int | Read

type ResM = () :+: Int           -- Ok | Reply Int

type Msg = (Pid RSing) :+:       -- LockM Pid
           ((Pid RSing) :+:      -- AcquiredM Pid
           ((Pid RSing, Cmd) :+: -- Req ProcessId Cmd
           (Pid RSing)))         -- Unlock Pid

type Ans = (Pid RSing, Int)      -- Ans Pid Int

write_msg :: ReslockSem repr => repr (Int -> Cmd)
write_msg = lam $ \n -> inl n
read_msg :: ReslockSem repr => repr Cmd
read_msg = inr tt

ok_msg :: ReslockSem repr => repr ResM
ok_msg = inl tt
reply_msg :: ReslockSem repr => repr (Int -> ResM)
reply_msg = lam $ \n -> inr n

lock_msg :: ReslockSem repr => repr (Pid RSing -> Msg)
lock_msg  = lam $ \pid -> inl pid
ack_msg :: ReslockSem repr => repr (Pid RSing -> Msg)
ack_msg  = lam $ \pid -> inr $ inl pid
req_msg :: ReslockSem repr => repr (Pid RSing -> Cmd -> Msg)
req_msg  = lam $ \pid -> lam $ \cmd -> inr $ inr $ inl $ pair pid cmd
unlock_msg :: ReslockSem repr => repr (Pid RSing -> Msg)
unlock_msg  = lam $ \pid -> inr $ inr $ inr pid

ans_msg :: ReslockSem repr => repr (Pid RSing -> Int -> Ans)
ans_msg  = lam $ \pid -> lam $ \n -> pair pid n

recv_lock :: ReslockSem repr => repr (Process (Pid RSing))
recv_lock  = do msg :: repr Msg <- recv
                ret $ match4 msg id fail fail fail
recv_ack :: ReslockSem repr => repr (Process (Pid RSing))
recv_ack  = do msg :: repr Msg <- recv
               ret $ match4 msg fail id fail fail
recv_req :: ReslockSem repr => repr (Process (Pid RSing, Cmd))
recv_req  = do msg :: repr Msg <- recv
               ret $ match4 msg fail fail id fail
recv_unlock :: ReslockSem repr => repr (Process (Pid RSing))
recv_unlock  = do msg :: repr Msg <- recv
                  ret $ match4 msg fail fail fail id

class ( Symantics repr
      , SymRecv   repr Msg
      , SymSend   repr Msg
      , SymRecv   repr Ans
      , SymSend   repr Ans
      , SymRecv   repr Res
      , SymSend   repr Res
      , SymRecv   repr Cmd
      , SymSend   repr Cmd
      ) => ReslockSem repr

-- LOCKED RESOURCE

res_start :: ReslockSem repr => repr (Res -> Process (Pid RSing))
res_start  = lam $ \res -> do r <- newRSing
                              spawn r (app res_free res)

res_free :: ReslockSem repr => repr (Res -> Process ())
res_free  = lam $ \res -> do p <- recv_lock
                             me <- self
                             send p (app ack_msg me)
                             app2 res_locked res p

res_locked :: ReslockSem repr => repr (Res -> Pid RSing -> Process ())
res_locked  = lam $ \res -> lam $ \p ->
                let req_h = lam $ \req -> -- req :: Req p cmd
                        let p      = proj1 req
                            cmd    = proj2 req
                            res'   = app3 query_res res p cmd -- res' :: (newres, r)
                            newres = proj1 res'
                            r      = proj2 res'
                            ok_h   = lam $ \_ -> app2 res_locked newres p
                            rep_h  = lam $ \a -> do me <- self
                                                    send p (app2 ans_msg me a)
                                                    app2 res_locked newres p
                         in match r ok_h rep_h
                    unl_h = lam $ \p -> app res_free res
                 in do msg :: repr Msg <- recv
                       match4 msg fail fail req_h unl_h

-- RES API

res_lock :: ReslockSem repr => repr (Pid RSing -> Process ())
res_lock  = lam $ \q -> do me <- self
                           send q (app lock_msg me)
                           ack <- recv_ack
                           ifte (eq ack q) (ret tt) fail

res_unlock :: ReslockSem repr => repr (Pid RSing -> Process ())
res_unlock  = lam $ \q -> do me <- self
                             send q (app unlock_msg me)
                             ret tt

res_request :: ReslockSem repr => repr (Pid RSing -> Cmd -> Process Int)
res_request  = lam $ \q -> lam $ \cmd ->
                 do me <- self
                    send q (app2 req_msg me cmd)
                    ans :: repr Ans <- recv
                    ifte (eq (proj1 ans) q) (ret (proj2 ans)) fail

res_do :: ReslockSem repr => repr (Pid RSing -> Cmd -> Process ())
res_do  = lam $ \q -> lam $ \cmd ->
            do me <- self
               send q (app2 req_msg me cmd)
               ret tt

-- CELL IMPLEMENTATION

type Res = Int

cell_start :: ReslockSem repr => repr (Process (Pid RSing))
cell_start  = app res_start (repI 0)

query_res :: ReslockSem repr => repr (Res -> Pid RSing -> Cmd -> (Res,ResM))
query_res  = lam $ \x -> lam $ \pid -> lam $ \cmd ->
               match cmd (lam $ \y -> pair y ok_msg) (lam $ \_ -> pair x (app reply_msg x))

cell_lock :: ReslockSem repr => repr (Pid RSing -> Process ())
cell_lock  = lam $ \c -> app res_lock c

cell_write :: ReslockSem repr => repr (Pid RSing -> Int -> Process ())
cell_write  = lam $ \c -> lam $ \x -> app2 res_do c (app write_msg x)

cell_read :: ReslockSem repr => repr (Pid RSing -> Process Int)
cell_read  = lam $ \c -> app2 res_request c read_msg

cell_unlock :: ReslockSem repr => repr (Pid RSing -> Process ())
cell_unlock  = lam $ \c -> app res_unlock c

-- INCREMENT CLIENT

inc :: ReslockSem repr => repr (Pid RSing -> Process ())
inc  = lam $ \c -> do app cell_lock c
                      v <- app cell_read c
                      app2 cell_write c (plus v (repI 1)) -- c = c + 1
                      app cell_unlock c

reslock_main :: ReslockSem repr => repr (Process ())
reslock_main  = do c <- cell_start
                   n <- app any_nat tt -- add n to c (which is 0)
                   app2 add_to_cell c n

add_to_cell :: ReslockSem repr => repr (Pid RSing -> Int -> Process ())
add_to_cell  = lam $ \c -> lam $ \n ->
                 ifte (eq n (repI 0))
                   (ret tt)
                   (do r <- newRSing
                       spawn r (app inc c)
                       app2 add_to_cell c n)
