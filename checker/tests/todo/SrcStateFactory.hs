{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcStateFactory where

import Prelude (($), undefined, String, Int, fromInteger, negate)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import Data.Either
import SrcHelper
import Symmetry.SymbEx

type Msg1 = (Pid RSing, Int) -- Msg1 Pid Int
type Msg2 = Int              -- Msg2 Int

class ( Symantics repr
      , SymSend   repr Msg1
      , SymRecv   repr Msg1
      , SymSend   repr Msg2
      , SymRecv   repr Msg2
      , SymTypes repr (Pid RSing) Int
      , SymMatch repr () () (Process Int)
      , SymTypes repr Int (Int -> Int -> Process Int)
      , SymTypes repr Int (Int -> Process Int)
      , SymMatch repr () () (Process (Int, Int -> Process Int))
      ) => SFSem repr

instance SFSem SymbEx

create_msg1 :: SFSem repr => repr (Pid RSing -> Int -> Msg1)
create_msg1  = lam $ \pid -> lam $ \n -> pair pid n

state_factory :: SFSem repr => repr (Process ())
state_factory  = do n1 <- app any_nat tt
                    funWithState <- app2 factory n1 (lam $ \_ -> lam $ \_ -> app any_nat tt)
                    n2 <- app any_nat tt
                    app2 call_loop n2 funWithState
                    ret tt

type T_fs = (Int,(Int -> Int -> Process Int))

f_state :: SFSem repr
        => repr ((T_fs -> Process T_fs) -> T_fs -> Process T_fs)
f_state  = lam $ \state -> lam $ \arg ->
             do let n        = proj1 arg
                let newstate = proj2 arg
                msg1 :: repr Msg1 <- recv
                let p     = proj1 msg1
                    input = proj2 msg1
                 in do m <- app2 newstate n input
                       send p (m :: repr Msg2)
                       app state $ pair m newstate

state :: SFSem repr => repr (Int -> (Int -> Int -> Process Int) -> Process ())
state  = lam $ \n -> lam $ \newstate ->
           do app (fixM f_state) (pair n newstate)
              ret tt

factory :: SFSem repr => repr (Int -> (Int -> Int -> Process Int) -> Process (Int -> Process Int))
factory  = lam $ \n -> lam $ \newstate ->
             do r  <- newRSing
                p  <- spawn r (app2 state n newstate)
                me <- self
                ret (lam $ \input ->
                       do send p (app2 create_msg1 me input)
                          s :: repr Msg2 <- recv
                          ret s)

type T_fcl = (Int,(Int -> Process Int))

f_call_loop :: SFSem repr
            => repr ((T_fcl -> Process T_fcl) -> T_fcl -> Process T_fcl)
f_call_loop  =lam $ \call_loop -> lam $ \arg ->
                do let n = proj1 arg
                   let f = proj2 arg
                   ifte (lt n (repI 1)) fail $
                     ifte (eq n (repI 1))
                       (do n <- app any_nat tt
                           n' <- app f n
                           ret $ pair n' f)
                       (do n <- app any_nat tt
                           app f n
                           app call_loop $ pair (plus n (repI (-1))) f)

call_loop :: SFSem repr => repr (Int -> (Int -> Process Int) -> Process Int)
call_loop  = lam $ \n -> lam $ \f ->
               do res <- app (fixM f_call_loop) $ pair n f
                  ret $ proj1 res
