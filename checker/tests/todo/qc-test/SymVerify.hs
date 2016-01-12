module SymVerify () where
import SymVector
import SymMap
import Language.Haskell.Liquid.Prelude
 
initialState :: State
initialState = undefined
 
initialSched :: State -> [PID]
initialSched = undefined
 
check :: ()
check = runState initialState (initialSched initialState)
runState
  state@State{state_x_3 = state_x_3,
              state_PtrR_vP_0_0 = state_PtrR_vP_0_0,
              state_PtrW_vP_0_0 = state_PtrW_vP_0_0,
              state_vP_0_Buf_0 = state_vP_0_Buf_0,
              state_PtrR_vP_1_0 = state_PtrR_vP_1_0,
              state_PtrW_vP_1_0 = state_PtrW_vP_1_0,
              state_vP_1_Buf_0 = state_vP_1_Buf_0, state_vP_0_PC = state_vP_0_PC,
              state_vP_1_PC = state_vP_1_PC}
  ((:) (PID_vP_0) sched)
  | ((==) state_vP_0_PC (0)) =
    runState
      state{state_PtrW_vP_1_0 = ((+) state_PtrW_vP_1_0 1),
            state_vP_1_Buf_0 =
              (setVec state_PtrW_vP_1_0 (VUnit) state_vP_1_Buf_0),
            state_vP_0_PC = (-1)}
      sched
runState
  state@State{state_x_3 = state_x_3,
              state_PtrR_vP_0_0 = state_PtrR_vP_0_0,
              state_PtrW_vP_0_0 = state_PtrW_vP_0_0,
              state_vP_0_Buf_0 = state_vP_0_Buf_0,
              state_PtrR_vP_1_0 = state_PtrR_vP_1_0,
              state_PtrW_vP_1_0 = state_PtrW_vP_1_0,
              state_vP_1_Buf_0 = state_vP_1_Buf_0, state_vP_0_PC = state_vP_0_PC,
              state_vP_1_PC = state_vP_1_PC}
  ((:) (PID_vP_1) sched)
  | ((&&) ((==) state_vP_1_PC (0))
       (((<) state_PtrR_vP_1_0 state_PtrW_vP_1_0)))
    =
    runState
      state{state_vP_1_PC = (-1),
            state_PtrR_vP_1_0 = ((+) state_PtrR_vP_1_0 1),
            state_x_3 = (getVec state_PtrR_vP_1_0 state_vP_1_Buf_0)}
      sched
runState
  state@State{state_x_3 = state_x_3,
              state_PtrR_vP_0_0 = state_PtrR_vP_0_0,
              state_PtrW_vP_0_0 = state_PtrW_vP_0_0,
              state_vP_0_Buf_0 = state_vP_0_Buf_0,
              state_PtrR_vP_1_0 = state_PtrR_vP_1_0,
              state_PtrW_vP_1_0 = state_PtrW_vP_1_0,
              state_vP_1_Buf_0 = state_vP_1_Buf_0, state_vP_0_PC = state_vP_0_PC,
              state_vP_1_PC = state_vP_1_PC}
  (PID_vP_0 : PID_vP_1 : _)
  | True =
    liquidAssert
      (not
         (((&&)
             (((&&) (((||) ((==) state_vP_0_PC (-1)) (False)))
                 (((||) ((==) state_vP_1_PC (-1))
                     ((((&&) ((==) state_vP_1_PC (0))
                          (((<=) state_PtrW_vP_1_0 state_PtrR_vP_1_0)))))))))
             (((||) (False)
                 ((((&&) ((==) state_vP_1_PC (0))
                      (((<=) state_PtrW_vP_1_0 state_PtrR_vP_1_0))))))))))
      ()
 
data Val = VUnit{}
         | VInt{vVInt0 :: Int}
         | VStr{vVStr0 :: String}
         | VPid{vVPid0 :: PID}
         | VInL{vVInL0 :: Val}
         | VInR{vVInR0 :: Val}
         | VPair{vVPair0 :: Val, vVPair1 :: Val}
 
data State = State{state_x_3 :: Val, state_PtrR_vP_0_0 :: Int,
                   state_PtrW_vP_0_0 :: Int, state_vP_0_Buf_0 :: Vec Val,
                   state_PtrR_vP_1_0 :: Int, state_PtrW_vP_1_0 :: Int,
                   state_vP_1_Buf_0 :: Vec Val, state_vP_0_PC :: Int,
                   state_vP_1_PC :: Int}
 
is_VUnit, is_VInt, is_VStr, is_VPid, is_VInL, is_VInR, is_VPair ::
            Val -> Bool
is_VUnit VUnit{} = True
is_VUnit _ = False
is_VInt VInt{} = True
is_VInt _ = False
is_VStr VStr{} = True
is_VStr _ = False
is_VPid VPid{} = True
is_VPid _ = False
is_VInL VInL{} = True
is_VInL _ = False
is_VInR VInR{} = True
is_VInR _ = False
is_VPair VPair{} = True
is_VPair _ = False
 
data PID_pre = PID_vP_0
             | PID_vP_1
             deriving Eq
 
type PID = PID_pre
is_PID_vP_0 (PID_vP_0) = True
is_PID_vP_0 _ = False
is_PID_vP_1 (PID_vP_1) = True
is_PID_vP_1 _ = False
 
nonDet :: [PID] -> Int
nonDet = undefined

{-@ assume initialState :: {v:State | (state_vP_0_PC v == 0 && state_PtrR_vP_0_0 v == 0 && 0 <= state_PtrR_vP_0_0 v && state_PtrW_vP_0_0 v == 0 && 0 <= state_PtrW_vP_0_0 v && state_PtrR_vP_0_0 v <= state_PtrW_vP_0_0 v) && (state_vP_1_PC v == 0 && state_PtrR_vP_1_0 v == 0 && 0 <= state_PtrR_vP_1_0 v && state_PtrW_vP_1_0 v == 0 && 0 <= state_PtrW_vP_1_0 v && state_PtrR_vP_1_0 v <= state_PtrW_vP_1_0 v)} @-}
{-@ assume initialSched :: initialState:State -> [PID_pre ] @-}
{-@  
data State = State{state_x_3 :: Val, state_PtrR_vP_0_0 :: Int,
                   state_PtrW_vP_0_0 :: Int, state_vP_0_Buf_0 :: Vec Val,
                   state_PtrR_vP_1_0 :: Int, state_PtrW_vP_1_0 :: Int,
                   state_vP_1_Buf_0 :: Vec Val, state_vP_0_PC :: Int,
                   state_vP_1_PC :: Int} @-}
{-@ measure is_PID_vP_0 @-}
{-@ measure is_PID_vP_1 @-}

{-@ measure is_VUnit @-}
{-@ measure is_VInt @-}
{-@ measure is_VStr @-}
{-@ measure is_VPid @-}
{-@ measure is_VInL @-}
{-@ measure is_VInR @-}
{-@ measure is_VPair @-}

{-@ qualif Deref_state_x_3(v:Val, x:State): v = state_x_3 x @-}
{-@ qualif Eq_state_x_3(v:State, x:State): state_x_3 v = state_x_3 x @-}
{-@ qualif Deref_state_PtrR_vP_0_0(v:Int, x:State): v = state_PtrR_vP_0_0 x @-}
{-@ qualif Eq_state_PtrR_vP_0_0(v:State, x:State): state_PtrR_vP_0_0 v = state_PtrR_vP_0_0 x @-}
{-@ qualif Deref_state_PtrW_vP_0_0(v:Int, x:State): v = state_PtrW_vP_0_0 x @-}
{-@ qualif Eq_state_PtrW_vP_0_0(v:State, x:State): state_PtrW_vP_0_0 v = state_PtrW_vP_0_0 x @-}
{-@ qualif Deref_state_vP_0_Buf_0(v:Vec Val, x:State): v = state_vP_0_Buf_0 x @-}
{-@ qualif Eq_state_vP_0_Buf_0(v:State, x:State): state_vP_0_Buf_0 v = state_vP_0_Buf_0 x @-}
{-@ qualif Deref_state_PtrR_vP_1_0(v:Int, x:State): v = state_PtrR_vP_1_0 x @-}
{-@ qualif Eq_state_PtrR_vP_1_0(v:State, x:State): state_PtrR_vP_1_0 v = state_PtrR_vP_1_0 x @-}
{-@ qualif Deref_state_PtrW_vP_1_0(v:Int, x:State): v = state_PtrW_vP_1_0 x @-}
{-@ qualif Eq_state_PtrW_vP_1_0(v:State, x:State): state_PtrW_vP_1_0 v = state_PtrW_vP_1_0 x @-}
{-@ qualif Deref_state_vP_1_Buf_0(v:Vec Val, x:State): v = state_vP_1_Buf_0 x @-}
{-@ qualif Eq_state_vP_1_Buf_0(v:State, x:State): state_vP_1_Buf_0 v = state_vP_1_Buf_0 x @-}
{-@ qualif Deref_state_vP_0_PC(v:Int, x:State): v = state_vP_0_PC x @-}
{-@ qualif Eq_state_vP_0_PC(v:State, x:State): state_vP_0_PC v = state_vP_0_PC x @-}
{-@ qualif Deref_state_vP_1_PC(v:Int, x:State): v = state_vP_1_PC x @-}
{-@ qualif Eq_state_vP_1_PC(v:State, x:State): state_vP_1_PC v = state_vP_1_PC x @-}


{-@  
data Val = VUnit{}
         | VInt{vVInt0 :: Int}
         | VStr{vVStr0 :: String}
         | VPid{vVPid0 :: PID}
         | VInL{vVInL0 :: Val}
         | VInR{vVInR0 :: Val}
         | VPair{vVPair0 :: Val, vVPair1 :: Val} @-}

{-@ nonDet :: [PID] -> {v:Int | true} @-}
