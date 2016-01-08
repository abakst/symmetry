module SymVerify () where
import Language.Haskell.Liquid.Prelude
 
initialState :: State
initialState = undefined
 
initialSched :: State -> [PID]
initialSched = undefined
 
check :: ()
check = runState initialState (initialSched initialState)
runState
  state@State{state_role_1 = state_role_1,
              state_vP_role_1_k = state_vP_role_1_k, state_x_5 = state_x_5,
              state_x_8 = state_x_8, state_vP_role_1_PCK = state_vP_role_1_PCK,
              state_vP_role_1_RdK = state_vP_role_1_RdK,
              state_vP_role_1_WrK = state_vP_role_1_WrK,
              state_PtrR_vP_0_0 = state_PtrR_vP_0_0,
              state_PtrW_vP_0_0 = state_PtrW_vP_0_0,
              state_vP_0_Buf_0 = state_vP_0_Buf_0,
              state_PtrR_vP_role_1_0 = state_PtrR_vP_role_1_0,
              state_PtrW_vP_role_1_0 = state_PtrW_vP_role_1_0,
              state_vP_role_1_Buf_0 = state_vP_role_1_Buf_0,
              state_vP_0_PC = state_vP_0_PC,
              state_vP_role_1_PC = state_vP_role_1_PC, state_x_7 = state_x_7}
  ((:) (PID_vP_0) sched)
  | ((==) state_vP_0_PC (0)) =
    runState
      state{state_vP_0_PC = 1,
            state_x_8 =
              let x_8' = (nonDet sched) in
                (liquidAssume ((&&) (((<=) 0 x_8')) (((<) x_8' state_role_1)))
                   x_8')}
      sched
  | ((==) state_vP_0_PC (1)) =
    runState
      state{state_PtrW_vP_role_1_0 =
              (put state_PtrW_vP_role_1_0 state_x_8
                 ((+) (get state_PtrW_vP_role_1_0 state_x_8) 1)),
            state_vP_role_1_WrK =
              (put state_vP_role_1_WrK 0 ((+) (get state_vP_role_1_WrK 0) 1)),
            state_vP_role_1_Buf_0 =
              (put state_vP_role_1_Buf_0 state_x_8
                 (put (get state_vP_role_1_Buf_0 state_x_8)
                    (get state_PtrW_vP_role_1_0 state_x_8)
                    (state_x_7))),
            state_vP_0_PC = (-1)}
      sched
runState
  state@State{state_role_1 = state_role_1,
              state_vP_role_1_k = state_vP_role_1_k, state_x_5 = state_x_5,
              state_x_8 = state_x_8, state_vP_role_1_PCK = state_vP_role_1_PCK,
              state_vP_role_1_RdK = state_vP_role_1_RdK,
              state_vP_role_1_WrK = state_vP_role_1_WrK,
              state_PtrR_vP_0_0 = state_PtrR_vP_0_0,
              state_PtrW_vP_0_0 = state_PtrW_vP_0_0,
              state_vP_0_Buf_0 = state_vP_0_Buf_0,
              state_PtrR_vP_role_1_0 = state_PtrR_vP_role_1_0,
              state_PtrW_vP_role_1_0 = state_PtrW_vP_role_1_0,
              state_vP_role_1_Buf_0 = state_vP_role_1_Buf_0,
              state_vP_0_PC = state_vP_0_PC,
              state_vP_role_1_PC = state_vP_role_1_PC, state_x_7 = state_x_7}
  ((:) (PID_vP_role_1 irole_1) sched)
  | ((&&) ((==) irole_1 state_vP_role_1_k)
       ((&&) ((==) (get state_vP_role_1_PC irole_1) (0))
          (((<) (get state_PtrR_vP_role_1_0 irole_1)
              (get state_PtrW_vP_role_1_0 irole_1)))))
    =
    runState
      state{state_vP_role_1_PC = (put state_vP_role_1_PC irole_1 (-1)),
            state_PtrR_vP_role_1_0 =
              (put state_PtrR_vP_role_1_0 irole_1
                 ((+) (get state_PtrR_vP_role_1_0 irole_1) 1)),
            state_vP_role_1_RdK =
              (put state_vP_role_1_RdK 0 ((+) (get state_vP_role_1_RdK 0) 1)),
            state_x_5 =
              (put state_x_5 irole_1
                 (get (get state_vP_role_1_Buf_0 irole_1)
                    (get state_PtrR_vP_role_1_0 irole_1)))}
      sched
  | ((&&) (not ((==) irole_1 state_vP_role_1_k))
       ((&&) ((==) (get state_vP_role_1_PC irole_1) (0))
          (((<) (get state_PtrR_vP_role_1_0 irole_1)
              (get state_PtrW_vP_role_1_0 irole_1)))))
    =
    runState
      state{state_vP_role_1_PC = (put state_vP_role_1_PC irole_1 (-1)),
            state_vP_role_1_PCK =
              (put
                 (put state_vP_role_1_PCK 0 ((-) (get state_vP_role_1_PCK 0) 1))
                 (-1)
                 ((+) (get state_vP_role_1_PCK (-1)) 1)),
            state_PtrR_vP_role_1_0 =
              (put state_PtrR_vP_role_1_0 irole_1
                 ((+) (get state_PtrR_vP_role_1_0 irole_1) 1)),
            state_vP_role_1_RdK =
              (put state_vP_role_1_RdK 0 ((+) (get state_vP_role_1_RdK 0) 1)),
            state_x_5 =
              (put state_x_5 irole_1
                 (get (get state_vP_role_1_Buf_0 irole_1)
                    (get state_PtrR_vP_role_1_0 irole_1)))}
      sched
runState
  state@State{state_role_1 = state_role_1,
              state_vP_role_1_k = state_vP_role_1_k, state_x_5 = state_x_5,
              state_x_8 = state_x_8, state_vP_role_1_PCK = state_vP_role_1_PCK,
              state_vP_role_1_RdK = state_vP_role_1_RdK,
              state_vP_role_1_WrK = state_vP_role_1_WrK,
              state_PtrR_vP_0_0 = state_PtrR_vP_0_0,
              state_PtrW_vP_0_0 = state_PtrW_vP_0_0,
              state_vP_0_Buf_0 = state_vP_0_Buf_0,
              state_PtrR_vP_role_1_0 = state_PtrR_vP_role_1_0,
              state_PtrW_vP_role_1_0 = state_PtrW_vP_role_1_0,
              state_vP_role_1_Buf_0 = state_vP_role_1_Buf_0,
              state_vP_0_PC = state_vP_0_PC,
              state_vP_role_1_PC = state_vP_role_1_PC, state_x_7 = state_x_7}
  (PID_vP_0 : PID_vP_role_1 irole_1 : _)
  | ((==) irole_1 state_vP_role_1_k) =
    liquidAssert
      (not
         (((&&)
             (((&&) (((||) ((==) state_vP_0_PC (-1)) (False)))
                 (((&&)
                     (((||) ((==) (get state_vP_role_1_PC irole_1) (-1))
                         ((((&&) ((==) (get state_vP_role_1_PC irole_1) (0))
                              (((<=) (get state_PtrW_vP_role_1_0 irole_1)
                                  (get state_PtrR_vP_role_1_0 irole_1))))))))
                     ((==)
                        ((+) (get state_vP_role_1_PCK (-1)) (get state_vP_role_1_PCK 0))
                        ((-) state_role_1 1))))))
             (((||) (False)
                 ((((&&) ((==) (get state_vP_role_1_PC irole_1) (0))
                      (((<=) (get state_PtrW_vP_role_1_0 irole_1)
                          (get state_PtrR_vP_role_1_0 irole_1)))))))))))
      ()
 
data Val = VUnit{}
         | VInt{vVInt0 :: Int}
         | VStr{vVStr0 :: String}
         | VPid{vVPid0 :: PID}
         | VInL{vVInL0 :: Val}
         | VInR{vVInR0 :: Val}
         | VPair{vVPair0 :: Val, vVPair1 :: Val}
 
data State = State{state_role_1 :: Int, state_vP_role_1_k :: Int,
                   state_x_5 :: Map_t Int Val, state_x_8 :: Int,
                   state_vP_role_1_PCK :: Map_t Int Int,
                   state_vP_role_1_RdK :: Map_t Int Int,
                   state_vP_role_1_WrK :: Map_t Int Int, state_PtrR_vP_0_0 :: Int,
                   state_PtrW_vP_0_0 :: Int, state_vP_0_Buf_0 :: Map_t Int Val,
                   state_PtrR_vP_role_1_0 :: Map_t Int Int,
                   state_PtrW_vP_role_1_0 :: Map_t Int Int,
                   state_vP_role_1_Buf_0 :: Map_t Int (Map_t Int Val),
                   state_vP_0_PC :: Int, state_vP_role_1_PC :: Map_t Int Int,
                   state_x_7 :: Val}
 
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
 
data PID_pre role_1 = PID_vP_0
                    | PID_vP_role_1 role_1
                    deriving Eq
 
type PID = PID_pre Int
is_PID_vP_0 (PID_vP_0) = True
is_PID_vP_0 _ = False
is_PID_vP_role_1 (PID_vP_role_1 irole_1) = True
is_PID_vP_role_1 _ = False
 
nonDet :: [PID] -> Int
nonDet = undefined
 
data Map_t k v
 
get :: Map_t k v -> k -> v
get = undefined
 
put :: Map_t k v -> k -> v -> Map_t k v
put = undefined

{-@ assume initialState :: {v:State | (state_vP_0_PC v == 0 && state_PtrR_vP_0_0 v == 0 && 0 <= state_PtrR_vP_0_0 v && state_PtrW_vP_0_0 v == 0 && 0 <= state_PtrW_vP_0_0 v && state_PtrR_vP_0_0 v <= state_PtrW_vP_0_0 v) && (state_role_1 v - 1 == Map_select (state_vP_role_1_PCK v) 0 && 0 == Map_select (state_vP_role_1_PC v) (state_vP_role_1_k v) && (0 <= state_vP_role_1_k v && state_vP_role_1_k v < state_role_1 v) && Map_select (state_vP_role_1_PCK v) (-1 : int) + Map_select (state_vP_role_1_PCK v) 0 == state_role_1 v - 1 && 0 == Map_select (state_vP_role_1_PCK v) (-1 : int))} @-}
{-@ assume initialSched :: initialState:State -> [PID_pre {v:Int | Map_select (state_vP_role_1_PC initialState) v == 0 && (0 <= v && v < state_role_1 initialState) && (Map_select (state_PtrR_vP_role_1_0 initialState) v <= 0 && 0 <= Map_select (state_PtrW_vP_role_1_0 initialState) v) && Map_select (state_PtrW_vP_role_1_0 initialState) v == 0 && 0 <= Map_select (state_PtrW_vP_role_1_0 initialState) v}] @-}
{-@  
data State = State{state_role_1 :: Int, state_vP_role_1_k :: Int,
                   state_x_5 :: Map_t Int Val, state_x_8 :: Int,
                   state_vP_role_1_PCK :: Map_t Int Int,
                   state_vP_role_1_RdK :: Map_t Int Int,
                   state_vP_role_1_WrK :: Map_t Int Int, state_PtrR_vP_0_0 :: Int,
                   state_PtrW_vP_0_0 :: Int, state_vP_0_Buf_0 :: Map_t Int Val,
                   state_PtrR_vP_role_1_0 :: Map_t Int Int,
                   state_PtrW_vP_role_1_0 :: Map_t Int Int,
                   state_vP_role_1_Buf_0 :: Map_t Int (Map_t Int Val),
                   state_vP_0_PC :: Int, state_vP_role_1_PC :: Map_t Int Int,
                   state_x_7 :: Val} @-}
{-@ measure is_PID_vP_0 @-}
{-@ measure is_PID_vP_role_1 @-}

{-@ measure is_VUnit @-}
{-@ measure is_VInt @-}
{-@ measure is_VStr @-}
{-@ measure is_VPid @-}
{-@ measure is_VInL @-}
{-@ measure is_VInR @-}
{-@ measure is_VPair @-}

{-@ qualif Deref_state_role_1(v:Int, x:State): v = state_role_1 x @-}
{-@ qualif Eq_state_role_1(v:State, x:State): state_role_1 v = state_role_1 x @-}
{-@ qualif Deref_state_vP_role_1_k(v:Int, x:State): v = state_vP_role_1_k x @-}
{-@ qualif Eq_state_vP_role_1_k(v:State, x:State): state_vP_role_1_k v = state_vP_role_1_k x @-}
{-@ qualif Deref_state_x_5(v:Map_t Int Val, x:State): v = state_x_5 x @-}
{-@ qualif Eq_state_x_5(v:State, x:State): state_x_5 v = state_x_5 x @-}
{-@ qualif Deref_state_x_8(v:Int, x:State): v = state_x_8 x @-}
{-@ qualif Eq_state_x_8(v:State, x:State): state_x_8 v = state_x_8 x @-}
{-@ qualif Deref_state_vP_role_1_PCK(v:Map_t Int Int, x:State): v = state_vP_role_1_PCK x @-}
{-@ qualif Eq_state_vP_role_1_PCK(v:State, x:State): state_vP_role_1_PCK v = state_vP_role_1_PCK x @-}
{-@ qualif Deref_state_vP_role_1_RdK(v:Map_t Int Int, x:State): v = state_vP_role_1_RdK x @-}
{-@ qualif Eq_state_vP_role_1_RdK(v:State, x:State): state_vP_role_1_RdK v = state_vP_role_1_RdK x @-}
{-@ qualif Deref_state_vP_role_1_WrK(v:Map_t Int Int, x:State): v = state_vP_role_1_WrK x @-}
{-@ qualif Eq_state_vP_role_1_WrK(v:State, x:State): state_vP_role_1_WrK v = state_vP_role_1_WrK x @-}
{-@ qualif Deref_state_PtrR_vP_0_0(v:Int, x:State): v = state_PtrR_vP_0_0 x @-}
{-@ qualif Eq_state_PtrR_vP_0_0(v:State, x:State): state_PtrR_vP_0_0 v = state_PtrR_vP_0_0 x @-}
{-@ qualif Deref_state_PtrW_vP_0_0(v:Int, x:State): v = state_PtrW_vP_0_0 x @-}
{-@ qualif Eq_state_PtrW_vP_0_0(v:State, x:State): state_PtrW_vP_0_0 v = state_PtrW_vP_0_0 x @-}
{-@ qualif Deref_state_vP_0_Buf_0(v:Map_t Int Val, x:State): v = state_vP_0_Buf_0 x @-}
{-@ qualif Eq_state_vP_0_Buf_0(v:State, x:State): state_vP_0_Buf_0 v = state_vP_0_Buf_0 x @-}
{-@ qualif Deref_state_PtrR_vP_role_1_0(v:Map_t Int Int, x:State): v = state_PtrR_vP_role_1_0 x @-}
{-@ qualif Eq_state_PtrR_vP_role_1_0(v:State, x:State): state_PtrR_vP_role_1_0 v = state_PtrR_vP_role_1_0 x @-}
{-@ qualif Deref_state_PtrW_vP_role_1_0(v:Map_t Int Int, x:State): v = state_PtrW_vP_role_1_0 x @-}
{-@ qualif Eq_state_PtrW_vP_role_1_0(v:State, x:State): state_PtrW_vP_role_1_0 v = state_PtrW_vP_role_1_0 x @-}
{-@ qualif Deref_state_vP_role_1_Buf_0(v:Map_t Int (Map_t Int Val), x:State): v = state_vP_role_1_Buf_0 x @-}
{-@ qualif Eq_state_vP_role_1_Buf_0(v:State, x:State): state_vP_role_1_Buf_0 v = state_vP_role_1_Buf_0 x @-}
{-@ qualif Deref_state_vP_0_PC(v:Int, x:State): v = state_vP_0_PC x @-}
{-@ qualif Eq_state_vP_0_PC(v:State, x:State): state_vP_0_PC v = state_vP_0_PC x @-}
{-@ qualif Deref_state_vP_role_1_PC(v:Map_t Int Int, x:State): v = state_vP_role_1_PC x @-}
{-@ qualif Eq_state_vP_role_1_PC(v:State, x:State): state_vP_role_1_PC v = state_vP_role_1_PC x @-}
{-@ qualif Deref_state_x_7(v:Val, x:State): v = state_x_7 x @-}
{-@ qualif Eq_state_x_7(v:State, x:State): state_x_7 v = state_x_7 x @-}


{-@  
data Val = VUnit{}
         | VInt{vVInt0 :: Int}
         | VStr{vVStr0 :: String}
         | VPid{vVPid0 :: PID}
         | VInL{vVInL0 :: Val}
         | VInR{vVInR0 :: Val}
         | VPair{vVPair0 :: Val, vVPair1 :: Val} @-}

{-@ nonDet :: [PID] -> {v:Int | true} @-}
{-@ embed Map_t as Map_t @-}
{-@ measure Map_select :: Map_t k v -> k -> v @-}
{-@ measure Map_store :: Map_t k v -> k -> v -> Map_t k v @-}
{-@ get :: m:Map_t k v -> k:k -> {v:v | v = Map_select m k} @-}
{-@ put :: m:Map_t k v -> k:k -> v:v -> {vv:Map_t k v | vv = Map_store m k v } @-}
