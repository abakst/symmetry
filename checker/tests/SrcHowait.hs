{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcHowait where

import Prelude (($), undefined, String, Int, fromInteger, negate)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import Data.Either
import SrcHelper

type Msg = (Pid RSing, Int)  :+: -- Reply   Pid Int
           ((Pid RSing, Int) :+: -- Request Pid Int
            (Pid RSing, Int))    -- Result  Pid Int

class ( Symantics repr
      , SymSend   repr Msg
      , SymRecv   repr Msg
      ) => HowaitSem repr

recv_reply :: HowaitSem repr => repr (Process (Pid RSing, Int))
recv_reply = do msg :: repr Msg <- recv
                return $ match msg id fail

reply_msg :: HowaitSem repr => repr (Pid RSing -> Int -> Msg)
reply_msg  = lam $ \pid -> lam $ \n -> inl $ pair pid n

recv_request :: HowaitSem repr => repr (Process (Pid RSing, Int))
recv_request  = do msg :: repr Msg <- recv
                   return $ match msg fail $ lam $ \e2 -> match e2 id fail

request_msg :: HowaitSem repr => repr (Pid RSing -> Int -> Msg)
request_msg  = lam $ \pid -> lam $ \n -> inr $ inl $ pair pid n

recv_result :: HowaitSem repr => repr (Process (Pid RSing, Int))
recv_result  = do msg :: repr Msg <- recv
                  return $ match msg fail $ lam $ \e2 -> match e2 fail id

result_msg :: HowaitSem repr => repr (Pid RSing -> Int -> Msg)
result_msg  = lam $ \pid -> lam $ \n -> inr $ inr $ pair pid n

howait :: HowaitSem repr => repr (Process ())
howait  = do n <- app any_nat tt
             r <- newRSing
             s <- spawn r serve
             app2 sp_wait1 (lam $ \x -> app2 client s x) n
             return tt

serve :: HowaitSem repr => repr (Process ())
serve  = do me  <- self
            req <- recv_request
            let p = proj1 req
                x = proj2 req
             in do send p (app2 reply_msg me (plus x (repI 1)))
                   serve


client :: HowaitSem repr => repr (Pid RSing -> Int -> Process Int)
client  = lam $ \s -> lam $ \n ->
            do me <- self
               send s (app2 request_msg me n)
               msg <- recv_reply
               ret (proj2 msg)

sp_wait1 :: HowaitSem repr => repr ((Int -> Process Int) -> Int -> Process [Int])
sp_wait1  = lam $ \f -> lam $ \n -> app3 sp_wait2 f (ret nil) n

sp_wait2 :: HowaitSem repr => repr ((Int -> Process Int) -> Process [Int] -> Int -> Process [Int])
sp_wait2  = lam $ \f -> lam $ \g -> lam $ \n ->
              ifte (eq n (repI 0))
                g
                (do me <- self
                    r <- newRSing
                    worker <- spawn r $ do res <- app f (plus n (repI 1))
                                           myself <- self
                                           send me (app2 result_msg myself res)
                    let helper = do msg <- recv_result
                                    let p = proj1 msg
                                        r = proj2 msg
                                     in ifte (eq p worker)
                                          (do l <- g
                                              return $ cons r l)
                                          fail
                     in app3 sp_wait2 f helper n)
