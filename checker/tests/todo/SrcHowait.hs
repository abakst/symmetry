{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=), (>>), fail, return, id)
import Symmetry.Language
import Symmetry.Verify
import SrcHelper

type Msg = (Pid RSing, Int)  :+: -- Reply   Pid Int
           ((Pid RSing, Int) :+: -- Request Pid Int
            (Pid RSing, Int))    -- Result  Pid Int

class ( HelperSym repr
      ) => HowaitSem repr

recv_reply :: HowaitSem repr => repr (Process repr (Pid RSing, Int))
recv_reply = do msg :: repr Msg <- recv
                match msg id (lam $ \_ -> die)

reply_msg :: HowaitSem repr => repr (Pid RSing -> Int -> Msg)
reply_msg  = lam $ \pid -> lam $ \n -> inl $ pair pid n

recv_request :: HowaitSem repr => repr (Process repr (Pid RSing, Int))
recv_request  = do msg :: repr Msg <- recv
                   match msg reject $ lam $ \e2 -> match e2 id reject

request_msg :: HowaitSem repr => repr (Pid RSing -> Int -> Msg)
request_msg  = lam $ \pid -> lam $ \n -> inr $ inl $ pair pid n

recv_result :: HowaitSem repr => repr (Process repr (Pid RSing, Int))
recv_result  = do msg :: repr Msg <- recv
                  match msg reject $ lam $ \e2 -> match e2 reject id

result_msg :: HowaitSem repr => repr (Pid RSing -> Int -> Msg)
result_msg  = lam $ \pid -> lam $ \n -> inr $ inr $ pair pid n

howait :: HowaitSem repr => repr (Process repr ())
howait  = do n <- app any_nat tt
             r <- newRSing
             s <- spawn r serve
             app2 sp_wait1 (lam $ \x -> app2 client s x) n
             return tt

serve :: HowaitSem repr => repr (Process repr ())
serve  = do let f_serve = lam $ \serve -> lam $ \_ ->
                           do me  <- self
                              req <- recv_request
                              let p = proj1 req
                              let x = proj2 req
                              send p (app2 reply_msg me (plus x (int 1)))
                              app serve tt
            app (fixM f_serve) tt


client :: HowaitSem repr => repr (Pid RSing -> Int -> Process repr Int)
client  = lam $ \s -> lam $ \n ->
            do me <- self
               send s (app2 request_msg me n)
               msg <- recv_reply
               ret (proj2 msg)

sp_wait1 :: HowaitSem repr => repr ((Int -> Process repr Int) -> Int -> Process repr [Int])
sp_wait1  = lam $ \f -> lam $ \n -> app3 sp_wait2 f (ret nil) n

type T_spw2 repr = ((Int -> Process repr Int),((Process repr [Int]), (Int, [Int])))

f_sp_wait2 :: HowaitSem repr
           => repr (((T_spw2 repr) -> Process repr (T_spw2 repr))
                    -> (T_spw2 repr) -> Process repr (T_spw2 repr))
f_sp_wait2  =
  lam $ \sp_wait2 -> lam $ \arg ->
  do let f = proj1 arg
         g = proj1 $ proj2 arg
         n = proj1 $ proj2 $ proj2 arg
         arg4 = proj2 $ proj2 $ proj2 arg
     ifte (eq n (int 0))
       (do l <- g
           ret $ pair4 f g n l)
       (do me <- self
           r <- newRSing
           worker <- spawn r $ do res    <- app f (plus n (int 1))
                                  myself <- self
                                  send me (app2 result_msg myself res)
           let helper = do msg <- recv_result
                           let p = proj1 msg
                               r = proj2 msg
                           ifte (eq p worker)
                             (do l <- g
                                 return $ cons r l)
                             fail
           app sp_wait2 $ pair4 f helper n arg4)

sp_wait2 :: HowaitSem repr
         => repr ((Int -> Process repr Int) -> Process repr [Int] -> Int -> Process repr [Int])
sp_wait2  = lam $ \f -> lam $ \g -> lam $ \n ->
              do res <- app (fixM f_sp_wait2) $ pair4 f g n nil
                 ret $ proj2 $ proj2 $ proj2 res

main :: IO ()
main  = checkerMain $ exec howait
