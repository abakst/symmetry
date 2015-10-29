{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return, id)
import Symmetry.Language
import Symmetry.Verify
import Symmetry.SymbEx
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

recv_lock :: ReslockSem repr => repr (Process repr (Pid RSing))
recv_lock  = do msg :: repr Msg <- recv
                match4 msg id reject reject reject
recv_ack :: ReslockSem repr => repr (Process repr (Pid RSing))
recv_ack  = do msg :: repr Msg <- recv
               match4 msg reject id reject reject
recv_req :: ReslockSem repr => repr (Process repr (Pid RSing, Cmd))
recv_req  = do msg :: repr Msg <- recv
               match4 msg reject reject id reject
recv_unlock :: ReslockSem repr => repr (Process repr (Pid RSing))
recv_unlock  = do msg :: repr Msg <- recv
                  match4 msg reject reject reject id

class ( HelperSym repr
      ) => ReslockSem repr

instance ReslockSem SymbEx

-- LOCKED RESOURCE
type T_rl = (Res, Pid RSing)

res_start :: ReslockSem repr => repr (Res -> Process repr (Pid RSing))
res_start  = lam $ \res -> do r <- newRSing
                              spawn r (app res_main res)

res_main :: forall repr. ReslockSem repr => repr (Res -> Process repr ())                                    
res_main = lam $ \res -> do app (fixM res_outer_loop) res
                            return tt
  where
    res_outer_loop = lam $ \loop -> lam $ \res -> do p <- recv_lock
                                                     me <- self
                                                     send p (app ack_msg me)
                                                     r <- app2 res_locked res p
                                                     app loop (proj1 r)

    res_locked :: ReslockSem repr => repr (Res -> Pid RSing -> Process repr (Res, Pid RSing))
    res_locked =  lam $ \res -> lam $ \p ->
                    app (fixM res_locked_loop) (pair res p)

    res_locked_loop =
      lam $ \loop -> lam $ \arg ->
                     do let res = proj1 arg
                            p   = proj2 arg
                            req_h = lam $ \req -> -- req :: Req p cmd
                                  do let p      = proj1 req
                                         cmd    = proj2 req
                                         res'   = app3 query_res res p cmd -- res' :: (newres, r)
                                         newres = proj1 res'
                                         r      = proj2 res'
                                         ok_h   = lam $ \_ -> app loop $ pair newres p
                                         rep_h  = lam $ \a ->
                                                    do me <- self
                                                       send p (app2 ans_msg me a)
                                                       app loop $ pair newres p
                                     match r ok_h rep_h
                            unl_h = lam $ \p -> return arg
                        msg :: repr Msg <- recv
                        match4 msg reject reject req_h unl_h
-- RES API

res_lock :: ReslockSem repr => repr (Pid RSing -> Process repr ())
res_lock  = lam $ \q -> do me <- self
                           send q (app lock_msg me)
                           ack <- recv_ack
                           ifte (eq ack q) (ret tt) fail

res_unlock :: ReslockSem repr => repr (Pid RSing -> Process repr ())
res_unlock  = lam $ \q -> do me <- self
                             send q (app unlock_msg me)
                             ret tt

res_request :: ReslockSem repr => repr (Pid RSing -> Cmd -> Process repr Int)
res_request  = lam $ \q -> lam $ \cmd ->
                 do me <- self
                    send q (app2 req_msg me cmd)
                    ans :: repr Ans <- recv
                    ifte (eq (proj1 ans) q) (ret (proj2 ans)) fail

res_do :: ReslockSem repr => repr (Pid RSing -> Cmd -> Process repr ())
res_do  = lam $ \q -> lam $ \cmd ->
            do me <- self
               send q (app2 req_msg me cmd)
               ret tt

-- CELL IMPLEMENTATION

type Res = Int

cell_start :: ReslockSem repr => repr (Process repr (Pid RSing))
cell_start  = app res_start (int 0)

query_res :: ReslockSem repr => repr (Res -> Pid RSing -> Cmd -> (Res,ResM))
query_res  = lam $ \x -> lam $ \pid -> lam $ \cmd ->
               match cmd (lam $ \y -> pair y ok_msg) (lam $ \_ -> pair x (app reply_msg x))

cell_lock :: ReslockSem repr => repr (Pid RSing -> Process repr ())
cell_lock  = lam $ \c -> app res_lock c

cell_write :: ReslockSem repr => repr (Pid RSing -> Int -> Process repr ())
cell_write  = lam $ \c -> lam $ \x -> app2 res_do c (app write_msg x)

cell_read :: ReslockSem repr => repr (Pid RSing -> Process repr Int)
cell_read  = lam $ \c -> app2 res_request c read_msg

cell_unlock :: ReslockSem repr => repr (Pid RSing -> Process repr ())
cell_unlock  = lam $ \c -> app res_unlock c

-- INCREMENT CLIENT

inc :: ReslockSem repr => repr (Pid RSing -> Process repr ())
inc  = lam $ \c -> do app cell_lock c
                      v <- app cell_read c
                      app2 cell_write c (plus v (int 1)) -- c = c + 1
                      app cell_unlock c

reslock_main :: ReslockSem repr => repr (Process repr ())
reslock_main  = do c <- cell_start
                   n <- app any_nat tt -- add n to c (which is 0)
                   app2 add_to_cell c n

add_to_cell :: ReslockSem repr => repr (Pid RSing -> Int -> Process repr ())
add_to_cell  = lam $ \c -> lam $ \n ->
                 do let fp = lam $ \arg ->
                               let c = proj1 arg
                                   n = proj2 arg
                                in ifte (eq n (int 0))
                                     (ret arg)
                                     (do r <- newRSing
                                         spawn r (app inc c)
                                         (ret arg))
                                         -- app add_to_cell (pair c n))
                    app fp (pair c n)
                    ret tt

main :: IO ()
main  = checkerMain $ exec reslock_main
