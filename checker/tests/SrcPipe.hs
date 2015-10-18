{-# LANGUAGE TypeOperators #-}
{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}

module SrcPipe where

import Prelude (($), undefined, Int, negate, fromInteger)
import Symmetry.Language.AST
import Symmetry.Language.Syntax
import GHC.Num ((+))
import Data.Either
import SrcHelper

class ( Symantics repr
      , SymSend   repr Int
      , SymRecv   repr Int
      ) => PipeSem repr

pipe :: PipeSem repr => repr (Process ())
pipe  = do me <- self
           n <- app any_nat tt
           head <- app (app (app init_pipe (lam $ \x -> plus (repI 1) x)) n) me
           send head (repI 0)
           sink

init_pipe :: PipeSem repr => repr ((Int->Int) -> Int -> (Pid RSing) -> Process (Pid RSing))
init_pipe  = lam $ \f -> lam $ \n -> lam $ \next ->
               ifte (eq n (repI 0))
                 (ret next)
                 (do role <- newRSing
                     new  <- spawn role (app (app pipe_node f) next)
                     pid  <- app (app (app init_pipe f) (plus n (repI (-1)))) new
                     ret pid)


sink :: PipeSem repr => repr (Process ())
sink  = do i :: repr Int <- recv
           die

pipe_node :: PipeSem repr => repr ((Int->Int) -> (Pid RSing) -> Process ())
pipe_node  = lam $ \f -> lam $ \next -> do i::repr Int <- recv
                                           send next (app f i)
                                           app (app pipe_node f) next
