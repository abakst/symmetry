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

type Msg1 = (Pid RSing, Int) -- Msg1 Pid Int
type Msg2 = Int              -- Msg2 Int

class ( Symantics repr
      , SymSend   repr Msg1
      , SymRecv   repr Msg1
      , SymSend   repr Msg2
      , SymRecv   repr Msg2
      , SymTypes repr (Pid RSing) Int
      , SymMatch repr () () (Process Int)
      ) => SFSem repr

create_msg1 :: SFSem repr => repr (Pid RSing -> Int -> Msg1)
create_msg1  = lam $ \pid -> lam $ \n -> pair pid n

state_factory :: SFSem repr => repr (Process ())
state_factory  = do n1 <- app any_nat tt
                    funWithState <- app2 factory n1 (lam $ \_ -> lam $ \_ -> app any_nat tt)
                    n2 <- app any_nat tt
                    app2 call_loop n2 funWithState
                    ret tt

state :: SFSem repr => repr (Int -> (Int -> Int -> Process Int) -> Process ())
state  = lam $ \n -> lam $ \newstate ->
           do msg1 :: repr Msg1 <- recv
              let p     = proj1 msg1
                  input = proj2 msg1
               in do m <- app2 newstate n input
                     send p (m :: repr Msg2)
                     app2 state m newstate

factory :: SFSem repr => repr (Int -> (Int -> Int -> Process Int) -> Process (Int -> Process Int))
factory  = lam $ \n -> lam $ \newstate ->
             do r  <- newRSing
                p  <- spawn r (app2 state n newstate)
                me <- self
                ret (lam $ \input ->
                       do send p (app2 create_msg1 me input)
                          s :: repr Msg2 <- recv
                          ret s)

call_loop :: SFSem repr => repr (Int -> (Int -> Process Int) -> Process Int)
call_loop  = lam $ \n -> lam $ \f ->
               ifte (lt n (repI 1)) fail $
                 ifte (eq n (repI 1))
                   (do n <- app any_nat tt
                       app f n)
                   (do n <- app any_nat tt
                       app f n
                       app2 call_loop (plus n (repI (-1))) f)
