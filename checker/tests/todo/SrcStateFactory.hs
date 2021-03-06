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

type Msg1 = (Pid RSing, Int) -- Msg1 Pid Int
type Msg2 = Int              -- Msg2 Int

class ( HelperSym repr
      ) => SFSem repr

instance SFSem SymbEx

create_msg1 :: SFSem repr => repr (Pid RSing -> Int -> Msg1)
create_msg1  = lam $ \pid -> lam $ \n -> pair pid n

state_factory :: SFSem repr => repr (Process repr ())
state_factory  = do let n1 = arb
                    funWithState <- app2 factory n1 (lam $ \_ -> lam $ \_ -> return arb)
                    let n2 = arb
                    app2 call_loop n2 funWithState
                    ret tt

type T_fs repr = (Int,(Int -> Int -> Process repr Int))

f_state :: SFSem repr
        => repr ((T_fs repr -> Process repr (T_fs repr)) -> T_fs repr
                 -> Process repr (T_fs repr))
f_state  = lam $ \state -> lam $ \arg ->
             do let n        = proj1 arg
                let newstate = proj2 arg
                msg1 :: repr Msg1 <- recv
                let p     = proj1 msg1
                    input = proj2 msg1
                 in do m <- app2 newstate n input
                       send p (m :: repr Msg2)
                       app state $ pair m newstate

state :: SFSem repr => repr (Int -> (Int -> Int -> Process repr Int) -> Process repr ())
state  = lam $ \n -> lam $ \newstate ->
           do app (fixM f_state) (pair n newstate)
              ret tt

factory :: SFSem repr => repr (Int -> (Int -> Int -> Process repr Int) -> Process repr (Int -> Process repr Int))
factory  = lam $ \n -> lam $ \newstate ->
             do r  <- newRSing
                p  <- spawn r (app2 state n newstate)
                me <- self
                ret (lam $ \input ->
                       do send p (app2 create_msg1 me input)
                          s :: repr Msg2 <- recv
                          ret s)

type T_fcl repr = (Int,(Int -> Process repr Int))

f_call_loop :: SFSem repr
            => repr ((T_fcl repr -> Process repr (T_fcl repr)) -> T_fcl repr
                     -> Process repr (T_fcl repr))
f_call_loop  =lam $ \call_loop -> lam $ \arg ->
                do let n = proj1 arg
                   let f = proj2 arg
                   ifte (lt n (int 1)) fail $
                     ifte (eq n (int 1))
                       (do let n = arb
                           n' <- app f n
                           ret $ pair n' f)
                       (do let n = arb
                           app f n
                           app call_loop $ pair (plus n (int (-1))) f)

call_loop :: SFSem repr => repr (Int -> (Int -> Process repr Int) -> Process repr Int)
call_loop  = lam $ \n -> lam $ \f ->
               do res <- app (fixM f_call_loop) $ pair n f
                  ret $ proj1 res

main :: IO ()
main  = checkerMain $ exec state_factory
