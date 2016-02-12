{-# Language RecordWildCards #-}
module SymVerify where
import SymVector
import SymMap
import SymBoilerPlate

import Control.Monad
import Data.Aeson

state0 :: State
state0 = undefined

sched0 :: State -> [Pid]
sched0 state = undefined

--check = runState state0 emptyVec emptyVec (sched0 state0) []
runState state@State{..} pidR0Buf0 pidR1Buf0 (PIDR0 : sched) stateList
  | (pidR0Pc == 0) =
    let s' = state{pidR1PtrW0 = pidR1PtrW0 + 1, pidR0Pc = (-1)}
    in runState s'
         pidR0Buf0
         (setVec pidR1PtrW0 VUnit pidR1Buf0)
         sched
         (s':stateList)

runState state@State{..} pidR0Buf0 pidR1Buf0 (PIDR1 : sched) stateList
  | ((pidR1Pc == 0) && (pidR1PtrR0 < pidR1PtrW0)) =
    let s' = state{pidR1PtrR0 = pidR1PtrR0 + 1,
               x_3 = (getVec pidR1PtrR0 pidR1Buf0), pidR1Pc = (-1)}
    in runState s'
         pidR0Buf0
         pidR1Buf0
         sched
         (s':stateList)

runState state@State{..} pidR0Buf0 pidR1Buf0
  (PIDR0 : (PIDR1 : sched)) stateList
  = liquidAssert
         (not
            ((((pidR1PtrW0 <= pidR1PtrR0) && (pidR1Pc == 0)) || False) &&
               ((((pidR1PtrW0 <= pidR1PtrR0) && (pidR1Pc == 0)) ||
                   (pidR1Pc == (-1)))
                  && (False || (pidR0Pc == (-1))))))
         $ stateList

runState _ _ _ _ _ = []

{-@ assume state0 :: {v:State | (pidR0Pc v == 0 && pidR0PtrR0 v == 0 && 0 <= pidR0PtrR0 v && pidR0PtrW0 v == 0 && 0 <= pidR0PtrW0 v && pidR0PtrR0 v <= pidR0PtrW0 v) && (pidR1Pc v == 0 && pidR1PtrR0 v == 0 && 0 <= pidR1PtrR0 v && pidR1PtrW0 v == 0 && 0 <= pidR1PtrW0 v && pidR1PtrR0 v <= pidR1PtrW0 v)} @-}
{-@ assume sched0 :: state0:State -> [Pid_pre ] @-}
{-@ data State = State{pidR0Pc :: Int, pidR1Pc :: Int,
                   pidR0PtrR0 :: Int, pidR1PtrR0 :: Int, pidR0PtrW0 :: Int,
                   pidR1PtrW0 :: Int, x_3 :: Val Pid_pre} @-}

{-@ qualif Deref_pidR0Pc(v:Int, w:State): v = pidR0Pc w @-}
{-@ qualif Eq_pidR0Pc(v:State, w:State ): pidR0Pc v = pidR0Pc w @-}
{-@ qualif Deref_pidR1Pc(v:Int, w:State): v = pidR1Pc w @-}
{-@ qualif Eq_pidR1Pc(v:State, w:State ): pidR1Pc v = pidR1Pc w @-}
{-@ qualif Deref_pidR0PtrR0(v:Int, w:State): v = pidR0PtrR0 w @-}
{-@ qualif Eq_pidR0PtrR0(v:State, w:State ): pidR0PtrR0 v = pidR0PtrR0 w @-}
{-@ qualif Deref_pidR1PtrR0(v:Int, w:State): v = pidR1PtrR0 w @-}
{-@ qualif Eq_pidR1PtrR0(v:State, w:State ): pidR1PtrR0 v = pidR1PtrR0 w @-}
{-@ qualif Deref_pidR0PtrW0(v:Int, w:State): v = pidR0PtrW0 w @-}
{-@ qualif Eq_pidR0PtrW0(v:State, w:State ): pidR0PtrW0 v = pidR0PtrW0 w @-}
{-@ qualif Deref_pidR1PtrW0(v:Int, w:State): v = pidR1PtrW0 w @-}
{-@ qualif Eq_pidR1PtrW0(v:State, w:State ): pidR1PtrW0 v = pidR1PtrW0 w @-}
{-@ qualif Deref_x_3(v:Val Pid_pre, w:State): v = x_3 w @-}
{-@ qualif Eq_x_3(v:State, w:State ): x_3 v = x_3 w @-}



data State = State{pidR0Pc :: Int, pidR1Pc :: Int,
                   pidR0PtrR0 :: Int, pidR1PtrR0 :: Int, pidR0PtrW0 :: Int,
                   pidR1PtrW0 :: Int, x_3 :: Val Pid_pre}
           deriving Show

data Pid_pre = PIDR0
             | PIDR1
             deriving Show
type Pid = Pid_pre
isPidR0 PIDR0 = (True)
isPidR0 _ = (False)
isPidR1 PIDR1 = (True)
isPidR1 _ = (False)


{-@ measure isPidR0 @-}
{-@ measure isPidR1 @-}



