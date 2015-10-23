{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

-- ::: COMPILE ERROR :::
-- tests/todo/SrcPipe.hs:30:10-23: No instance for (AbsValToIL (Int -> Int)) …
--       (maybe you haven't applied enough arguments to a function?)
--       arising from the superclasses of an instance declaration
--     In the instance declaration for ‘PipeSem SymbEx’

module Main where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import GHC.Num ((+))
import Data.Either
import SrcHelper
import Symmetry.Language
import Symmetry.Verify
import Symmetry.SymbEx

class ( Symantics repr
      , ArbPat repr ()
      , ArbPat repr Int
      ) => PipeSem repr

instance PipeSem SymbEx

pipe :: PipeSem repr => repr (Process repr ())
pipe  = do me   <- self
           n    <- app any_nat tt
           head <- app3 init_pipe (lam $ \x -> plus (int 1) x) n me
           send head (int 0)
           sink

type T_p = ((Int->Int),(Int,(Pid RSing)))

fix_init_pipe :: PipeSem repr
              => repr ((T_p -> Process repr T_p) -> T_p -> Process repr T_p)
fix_init_pipe  = lam $ \init_pipe -> lam $ \arg ->
                   let f    = proj1 arg
                       n    = proj1 $ proj2 arg
                       next = proj2 $ proj2 arg in
                   ifte (eq n (int 0))
                     (ret arg)
                     (do role <- newRSing
                         new  <- spawn role $ app2 pipe_node f next
                         app init_pipe $ pair3 f (plus n (int (-1))) new)


init_pipe :: PipeSem repr => repr ((Int->Int) -> Int -> (Pid RSing) -> Process repr (Pid RSing))
init_pipe  = lam $ \f -> lam $ \n -> lam $ \next ->
               do let p = pair3 f n next
                  p' <- app (fixM fix_init_pipe) p
                  let pid' = proj2 $ proj2 p'
                  return pid'

sink :: PipeSem repr => repr (Process repr ())
sink  = do i :: repr Int <- recv
           die

type T_p2 = ((Int->Int),(Pid RSing))

pipe_node :: PipeSem repr
          => repr ((Int->Int) -> (Pid RSing) -> Process repr ())
pipe_node  = lam $ \f -> lam $ \next ->
               do let fix_pn = lam $ \pipe_node -> lam $ \p ->
                                 do let f    = proj1 p
                                    let next = proj2 p
                                    i :: repr Int <- recv
                                    send next (app f i)
                                    app pipe_node p
                  app (fixM fix_pn) (pair f next)
                  ret tt


main :: IO ()
main  = checkerMain $ exec pipe
