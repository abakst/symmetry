module SymVerify () where
import SymVector
-- import SymMap
import Language.Haskell.Liquid.Prelude
 
initialState :: State
initialState = undefined
 
initialSched :: State -> [PID]
initialSched = undefined
 
{-@ check :: {v:() | true} @-}
check :: ()
check = runState initialState emptyVec (initialSched initialState)

{-@ runState :: state:{v:State | (stateVPRole0PC v = 2 => stateVPRole2PtrW0 v = 0) &&
                           (stateVPRole0PC v = 3 => stateVPRole2PtrW0 v = 0) &&
                           (stateVPRole0PC v = 4 => stateVPRole2PtrW0 v >= 0) &&
                           (stateVPRole0PC v = -1 => stateVPRole2PtrW0 v >= 1) &&
                           (stateVPRole0PC v = 1 => stateVPRole2PtrW0 v = 0) &&
                           (~ (isVInL (stateX_8 v)  && isVInR (stateX_8 v))) &&
                           
                           (stateVPRole2PC v = 0 => ~isVUnInit (stateX_8 v) => isVInL (stateX_8 v)) &&
                           (stateVPRole2PC v = 2 => ~isVUnInit (stateX_8 v) => isVInL (stateX_8 v)) &&
                           (stateVPRole2PC v = 3 => (~isVUnInit (stateX_8 v))) &&
                           (stateVPRole2PC v = 4 => (~isVUnInit (stateX_8 v) => isVInL (stateX_8 v))) &&
                           (stateVPRole2PC v = 5 => (~isVUnInit (stateX_8 v))) &&
                           (stateVPRole2PtrR0 v = 0 <=> isVUnInit (stateX_8 v)) &&

                           ((isVInL (stateX_8 v) && stateVPRole0PC v = -1) => 
                            (stateVPRole2PtrR0 v < stateVPRole2PtrW0 v)) &&

                           (stateVPRole2PtrW0 v >= 0) &&
                           (stateVPRole2PtrR0 v >= 0) &&
                           (stateVPRole2PtrR0 v <= stateVPRole2PtrW0 v)}
             -> Vec <{\i -> 0 <= i && i < stateVPRole2PtrW0 state},{\i v -> (0 <= i && i < stateVPRole2PtrW0 state && (if (stateVPRole0PC state = -1 && stateVPRole2PtrW0 state = i + 1) then (isVInR v && ~isVInL v) else (isVInL v && ~isVInR v))) && (~ isVUnInit v) }> Val
             -> [PID]
             -> ()
@-}
runState :: State -> Vec Val -> [PID] -> ()
runState
  state@State{stateX_8 = stateX_8, stateX_5 = stateX_5,
              stateL3 = stateL3, stateVPRole0PtrR0 = stateVPRole0PtrR0,
              stateVPRole0PtrW0 = stateVPRole0PtrW0,
              stateVPRole0Buf0 = stateVPRole0Buf0,
              stateVPRole2PtrR0 = stateVPRole2PtrR0,
              stateVPRole2PtrW0 = stateVPRole2PtrW0,
              stateVPRole2Buf0 = stateVPRole2Buf0,
              stateVPRole0PC = stateVPRole0PC, stateVPRole2PC = stateVPRole2PC}
  buf
  ((:) (PIDVPRole0) sched)
  | ((&&) ((==) (nonDet sched) 2) ((==) stateVPRole0PC (1))) =
    runState state{stateVPRole0PC = 2} buf sched
  | ((&&) ((==) (nonDet sched) 3) ((==) stateVPRole0PC (1))) =
    runState state{stateVPRole0PC = 3} buf sched
  | ((==) stateVPRole0PC (2)) =
    runState
      state{stateVPRole2PtrW0 = ((+) stateVPRole2PtrW0 1),
            stateVPRole0PC = 4}
      (setVec stateVPRole2PtrW0 ((VInL VUnit)) buf)
      sched
  | ((==) stateVPRole0PC (3)) =
    runState state{stateVPRole0PC = 4} buf sched
  | ((==) stateVPRole0PC (4)) =
    let 
        s = state{stateVPRole2PtrW0 = ((+) stateVPRole2PtrW0 1),
                  stateVPRole0PC = (-1)}
      in
         runState
          s
          (setVec stateVPRole2PtrW0 (VInR VUnit) buf)
          sched
runState
  state@State{stateX_8 = stateX_8, stateX_5 = stateX_5,
              stateL3 = stateL3, stateVPRole0PtrR0 = stateVPRole0PtrR0,
              stateVPRole0PtrW0 = stateVPRole0PtrW0,
              stateVPRole0Buf0 = stateVPRole0Buf0,
              stateVPRole2PtrR0 = stateVPRole2PtrR0,
              stateVPRole2PtrW0 = stateVPRole2PtrW0,
              stateVPRole2Buf0 = stateVPRole2Buf0,
              stateVPRole0PC = stateVPRole0PC, stateVPRole2PC = stateVPRole2PC}
  buf
  ((:) (PIDVPRole2) sched)
  | ((==) stateVPRole2PC (0)) =
    runState state{stateVPRole2PC = 2} buf sched
  | ((&&) ((==) stateVPRole2PC (2))
       (((<) stateVPRole2PtrR0 stateVPRole2PtrW0)))
    =
    runState
      state{stateVPRole2PC = 3,
            stateVPRole2PtrR0 = ((+) stateVPRole2PtrR0 1),
            stateX_8 = (getVec stateVPRole2PtrR0 buf)}
      buf
      sched
  | ((==) stateVPRole2PC (3)) =
    case stateX_8 of
        VInL x_5
          | True ->
            runState state{stateVPRole2PC = 4, stateX_5 = x_5} buf sched
        VInR x_5
          | True -> runState state{stateVPRole2PC = 5, stateX_5 = x_5} buf sched
  | ((==) stateVPRole2PC (4)) =
    runState state{stateVPRole2PC = 0} buf sched
  | ((==) stateVPRole2PC (5)) =
    runState state{stateVPRole2PC = (-1)} buf sched
runState
  state@State{stateX_8 = stateX_8, stateX_5 = stateX_5,
              stateL3 = stateL3, stateVPRole0PtrR0 = stateVPRole0PtrR0,
              stateVPRole0PtrW0 = stateVPRole0PtrW0,
              stateVPRole0Buf0 = stateVPRole0Buf0,
              stateVPRole2PtrR0 = stateVPRole2PtrR0,
              stateVPRole2PtrW0 = stateVPRole2PtrW0,
              stateVPRole2Buf0 = stateVPRole2Buf0,
              stateVPRole0PC = stateVPRole0PC, stateVPRole2PC = stateVPRole2PC}
  buf
  (PIDVPRole0 : PIDVPRole2 : _)
  | True =
    liquidAssert
      (not
         (((&&)
             (((&&) (((||) ((==) stateVPRole0PC (-1)) (False)))
                 (((||) ((==) stateVPRole2PC (-1))
                     ((((&&) ((==) stateVPRole2PC (2))
                          (((<=) stateVPRole2PtrW0 stateVPRole2PtrR0)))))))))
             (((||) (False)
                 ((((&&) ((==) stateVPRole2PC (2))
                      (((<=) stateVPRole2PtrW0 stateVPRole2PtrR0))))))))))
      ()
 
data Val = VUnit{}
         | VUnInit
         | VInt{vVInt0 :: Int}
         | VStr{vVStr0 :: String}
         | VPid{vVPid0 :: PID}
         | VInL{vVInL0 :: Val}
         | VInR{vVInR0 :: Val}
         | VPair{vVPair0 :: Val, vVPair1 :: Val}
 
data State = State{stateX_8 :: Val, stateX_5 :: Val,
                   stateL3 :: Int, stateVPRole0PtrR0 :: Int, stateVPRole0PtrW0 :: Int,
                   stateVPRole0Buf0 :: Vec Val, stateVPRole2PtrR0 :: Int,
                   stateVPRole2PtrW0 :: Int,
                   stateVPRole0PC :: Int, stateVPRole2PC :: Int,
                   stateVPRole2Buf0 :: Vec Val
                  }

{-@ data State = State  { stateX_8 :: Val, stateX_5 :: Val, stateL3 :: Int, stateVPRole0PtrR0 :: Int, stateVPRole0PtrW0 :: Int, stateVPRole0Buf0 :: Vec Val, stateVPRole2PtrR0 :: Int, stateVPRole2PtrW0 :: Int, stateVPRole0PC :: Int, stateVPRole2PC :: Int, stateVPRole2Buf0 :: Vec Val } @-}

isVUnit, isVInt, isVStr, isVPid, isVInL, isVInR, isVPair ::
           Val -> Bool
isVUnit VUnit{} = True
isVUnit _ = False
isVUnInit VUnInit{} = True
isVUnInit _ = False
isVInt VInt{} = True
isVInt _ = False
isVStr VStr{} = True
isVStr _ = False
isVPid VPid{} = True
isVPid _ = False
isVInL VInL{} = True
isVInL _ = False
isVInR VInR{} = True
isVInR _ = False
isVPair VPair{} = True
isVPair _ = False
 
data PID_pre = PIDVPRole0
             | PIDVPRole2
             deriving Eq
 
type PID = PID_pre
isPIDVPRole0 (PIDVPRole0) = True
isPIDVPRole0 _ = False
isPIDVPRole2 (PIDVPRole2) = True
isPIDVPRole2 _ = False
 
{-@ nonDet :: [PID] -> Int @-}
nonDet :: [PID] -> Int
nonDet = undefined

{-@ initialState :: {v:State | (isVUnInit (stateX_8 v)) && ~ ((isVInR (stateX_8 v)) && (isVInL (stateX_8 v))) && (stateVPRole0PC v == 1 && stateVPRole0PtrR0 v == 0 && 0 <= stateVPRole0PtrR0 v && stateVPRole0PtrW0 v == 0 && 0 <= stateVPRole0PtrW0 v && stateVPRole0PtrR0 v <= stateVPRole0PtrW0 v) && (stateVPRole2PC v == 0 && stateVPRole2PtrR0 v == 0 && 0 <= stateVPRole2PtrR0 v && stateVPRole2PtrW0 v == 0 && 0 <= stateVPRole2PtrW0 v && stateVPRole2PtrR0 v <= stateVPRole2PtrW0 v)} @-}
{-@ initialSched :: initialState:State -> [PID_pre ] @-}


{-@ measure isPIDVPRole0 @-}
{-@ measure isPIDVPRole2 @-}

{-@ measure isVUnit @-}
{-@ measure isVInt @-}
{-@ measure isVStr @-}
{-@ measure isVPid @-}
{-@ measure isVInL @-}
{-@ measure isVInR @-}
{-@ measure isVPair @-}
{-@ measure isVUnInit @-}

{-@ qualif Deref_stateX_8(v:Val, x:State): v = stateX_8 x @-}
{-@ qualif Eq_stateX_8(v:State, x:State): stateX_8 v = stateX_8 x @-}
{-@ qualif Deref_stateX_5(v:Val, x:State): v = stateX_5 x @-}
{-@ qualif Eq_stateX_5(v:State, x:State): stateX_5 v = stateX_5 x @-}
{-@ qualif Deref_stateL3(v:Int, x:State): v = stateL3 x @-}
{-@ qualif Eq_stateL3(v:State, x:State): stateL3 v = stateL3 x @-}
{-@ qualif Deref_stateVPRole0PtrR0(v:Int, x:State): v = stateVPRole0PtrR0 x @-}
{-@ qualif Eq_stateVPRole0PtrR0(v:State, x:State): stateVPRole0PtrR0 v = stateVPRole0PtrR0 x @-}
{-@ qualif Deref_stateVPRole0PtrW0(v:Int, x:State): v = stateVPRole0PtrW0 x @-}
{-@ qualif Eq_stateVPRole0PtrW0(v:State, x:State): stateVPRole0PtrW0 v = stateVPRole0PtrW0 x @-}
{-@ qualif Eq_stateVPRole0Buf0(v:State, x:State): stateVPRole0Buf0 v = stateVPRole0Buf0 x @-}
{-@ qualif Deref_stateVPRole2PtrR0(v:Int, x:State): v = stateVPRole2PtrR0 x @-}
{-@ qualif Eq_stateVPRole2PtrR0(v:State, x:State): stateVPRole2PtrR0 v = stateVPRole2PtrR0 x @-}
{-@ qualif Deref_stateVPRole2PtrW0(v:Int, x:State): v = stateVPRole2PtrW0 x @-}
{-@ qualif Eq_stateVPRole2PtrW0(v:State, x:State): stateVPRole2PtrW0 v = stateVPRole2PtrW0 x @-}
{-@ qualif Eq_stateVPRole2Buf0(v:State, x:State): stateVPRole2Buf0 v = stateVPRole2Buf0 x @-}
{-@ qualif Deref_stateVPRole0PC(v:Int, x:State): v = stateVPRole0PC x @-}
{-@ qualif Eq_stateVPRole0PC(v:State, x:State): stateVPRole0PC v = stateVPRole0PC x @-}
{-@ qualif Deref_stateVPRole2PC(v:Int, x:State): v = stateVPRole2PC x @-}
{-@ qualif Eq_stateVPRole2PC(v:State, x:State): stateVPRole2PC v = stateVPRole2PC x @-}


{-@  
data Val = VUnit{}
         | VUnInit{}
         | VInt{vVInt0 :: Int}
         | VStr{vVStr0 :: String}
         | VPid{vVPid0 :: PID}
         | VInL{vVInL0 :: Val}
         | VInR{vVInR0 :: Val}
         | VPair{vVPair0 :: Val, vVPair1 :: Val} @-}
