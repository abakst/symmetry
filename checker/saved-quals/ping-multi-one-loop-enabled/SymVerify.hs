{-# Language RecordWildCards #-}
{-@ LIQUID "--no-true-types" @-}
module SymVerify where
import SymVector
import SymMap
import SymBoilerPlate
import Data.Set
import Language.Haskell.Liquid.Prelude


state0 :: State
state0 = undefined

sched0 :: State -> [Pid]
sched0 state = undefined

{-@ assume instR1 :: forall <p :: Int -> Prop>. x:Int -> [Pid_pre Int<p>] -> {v:Int<p> | v = x} @-}
instR1 :: Int -> [Pid] -> Int
instR1 x _ = x
               
{-@ check :: {v:_ | true} @-}
check = runState state0 emptyVec emptyVec2D (sched0 state0)

{-@ predicate Buf0ValI I V   = true @-}
{-@ predicate Buf1ValI I J V = isPidR0 (vPid V) @-}

{-@ 
predicate StateI S =
  0 < r1 S &&
  0 <= xl0 S && xl0 S <= r1 S &&
  ((1 <= pidR0Pc S && pidR0Pc S <= 4) => (xl0 S < r1 S)) &&
  (pidR0Pc S = (-1) => xl0 S = r1 S) &&
  pidR0PtrR0 S = xl0 S + (if (pidR0Pc S = 4) then 1 else 0) &&
  (Map_select (pidR1PcK S) 0 + Map_select (pidR1PcK S) 1 + Map_select (pidR1PcK S) 2 + Map_select (pidR1PcK S) (-1) = r1 S) &&
  ((pidR0Pc S = 3 && Map_select (pidR1Pc S) (xl0 S) /= (-1)) => (Set_mem (xl0 S) (pidR1Enabled S))) &&
  ((pidR0Pc S = 3 && pidR0PtrW0 S = pidR0PtrR0 S) => (Map_select (pidR1Pc S) (xl0 S) /= (-1))) &&
  pidR0PtrR0 S <= pidR0PtrW0 S
@-}

{-@ 
predicate R1Inv S V = 
  (0 <= V && V < r1 S) &&
  (Map_select (pidR1Pc S) V = 2 => isPidR0 (vPid (Map_select (x2 S) V))) &&

  (Map_select (pidR1PtrW0 S) V = (if (V < xl0 S || (V = xl0 S && (pidR0Pc S = 3 || pidR0Pc S = 4))) then 1 else 0)) &&
  (Map_select (pidR1PtrR0 S) V = (if (0 = Map_select (pidR1Pc S) V || 1 = Map_select (pidR1Pc S) V) then 0 else 1)) &&

  ((Set_mem V (pidR1Enabled S) <=> ((Map_select (pidR1Pc S) V != (-1) && 
                                    (Map_select (pidR1Pc S) V != 1 || 
                                     Map_select (pidR1PtrR0 S) V < Map_select (pidR1PtrW0 S) V ))))) &&

  ((V >= (xl0 S) && (pidR0Pc S = 2 || pidR0Pc S = 1 || pidR0Pc S = 0)) => (Map_select (pidR1Pc S) V = 0 || Map_select (pidR1Pc S) V = 1)) &&
  ((V > (xl0 S) && (pidR0Pc S = 3 || pidR0Pc S = 4))                   => (Map_select (pidR1Pc S) V = 0 || Map_select (pidR1Pc S) V = 1)) &&

  (Map_select (pidR1PcK S) (-1) = pidR0PtrW0 S)
@-}
        
{-@ runState :: s:{v:_ | StateI v }
             -> Vec <\i -> {v:_ | Buf0ValI i v}> (Val Pid)
             -> Vec2D <\i j -> {v:_ | Buf1ValI i j v}> (Val Pid)
             -> [Pid_pre {v:Int | R1Inv s v}]
             -> ()
@-}
runState :: State -> Vec (Val Pid) -> Vec2D (Val Pid) -> [Pid] -> ()
runState state@State{..} pidR0Buf0 pidR1Buf0 (PIDR0 : sched)
  | ((pidR0Pc == 0) && (xl0 < r1)) =
    runState (t_pidR0_0 state) pidR0Buf0 pidR1Buf0 sched
  | ((pidR0Pc == 0) && (not (xl0 < r1))) =
    runState (t_pidR0_1 state) pidR0Buf0 pidR1Buf0 sched
  | (pidR0Pc == 1) =
    runState (t_pidR0_2 state) pidR0Buf0 pidR1Buf0 sched
  | (pidR0Pc == 2)  =
    runState (t_pidR0_3 state) pidR0Buf0
      (setVec2D (instR1 xl0 sched) (get pidR1PtrW0 (instR1 xl0 sched)) (VPid PIDR0) pidR1Buf0)
      sched
  | ((pidR0Pc == 3) && (pidR0PtrR0 < pidR0PtrW0)) =
    runState (t_pidR0_4 state ((getVec pidR0PtrR0 pidR0Buf0)))
      pidR0Buf0
      pidR1Buf0
      sched
  | (pidR0Pc == 4) =
    runState (t_pidR0_5 state) pidR0Buf0 pidR1Buf0 sched
runState state@State{..} pidR0Buf0 pidR1Buf0 ((PIDR1 ir1) : sched)
  | ((get pidR1Pc ir1) == 0)  && get pidR1PcK 0 > 0 =
    runState (t_pidR1_0 state ir1) pidR0Buf0 pidR1Buf0 sched
  | (((get pidR1Pc ir1) == 1) && get pidR1PcK 1 > 0 &&
       ((get pidR1PtrR0 ir1) < (get pidR1PtrW0 ir1)))
    =
    runState
      (t_pidR1_1 state ir1
         ((put x2 ir1 (getVec2D ir1 (get pidR1PtrR0 ir1) pidR1Buf0))))
      pidR0Buf0
      pidR1Buf0
      sched
  | ((get pidR1Pc ir1) == 2) && get pidR1PcK 2 > 0 {- && (ir1 `member` pidR1Enabled) -}=
    case (get x2 ir1) of
        VPid PIDR0 -> 
          runState (t_pidR1_2 state ir1)
                        (setVec pidR0PtrW0 (VPid (PIDR1 ir1)) pidR0Buf0)
                        pidR1Buf0
                        sched
        VPid (PIDR1 ir1) -> runState (t_pidR1_3 state ir1) pidR0Buf0
                              (setVec2D ir1 (get pidR1PtrW0 ir1) (VPid (PIDR1 ir1)) pidR1Buf0)
                              sched
runState state@State{..} pidR0Buf0 pidR1Buf0
  [(PIDR1 ir1_0), (PIDR1 ir1_1)]
  | ((pidR0Pc == (-1) || ((pidR0Pc == 3) && (pidR0PtrW0 <= pidR0PtrR0))) &&
     (empty == pidR1Enabled && ((get pidR1Pc ir1_0 == 1 && get pidR1PtrW0 ir1_0 <= get pidR1PtrR0 ir1_0 && get pidR1PcK 1 > 0) || (get pidR1Pc ir1_1 == (-1) && get pidR1PcK (-1) == r1))))
    = liquidAssert (get pidR1Pc ir1_1 == -1) $
      liquidAssert (pidR0Pc == -1) ()

runState state a0 a1 (s : sched) = runState state a0 a1 sched
{-@ assume t_pidR0_0 :: s0:{v:State | true} -> {s1:State | pidR1Enabled s1 = pidR1Enabled s0 && x0 s1 = x0 s0 && r1 s1 = r1 s0 && pidR1PcK s1 = pidR1PcK s0 && pidR1NumBlocked s1 = pidR1NumBlocked s0 && pidR0Pc s1 = 1 && pidR1Pc s1 = pidR1Pc s0 && pidR0PtrR0 s1 = pidR0PtrR0 s0 && pidR0PtrW0 s1 = pidR0PtrW0 s0 && pidR1PtrR0 s1 = pidR1PtrR0 s0 && pidR1PtrW0 s1 = pidR1PtrW0 s0 && x4 s1 = x4 s0 && x2 s1 = x2 s0 && xl0 s1 = xl0 s0} @-}
t_pidR0_0 :: State -> State
t_pidR0_0 state@State{..} = state{pidR0Pc = 1}

{-@ assume t_pidR0_1 :: s0:{v:State | true} -> {s1:State | pidR1Enabled s1 = pidR1Enabled s0 && x0 s1 = x0 s0 && r1 s1 = r1 s0 && pidR1PcK s1 = pidR1PcK s0 && pidR1NumBlocked s1 = pidR1NumBlocked s0 && pidR0Pc s1 = (-1) && pidR1Pc s1 = pidR1Pc s0 && pidR0PtrR0 s1 = pidR0PtrR0 s0 && pidR0PtrW0 s1 = pidR0PtrW0 s0 && pidR1PtrR0 s1 = pidR1PtrR0 s0 && pidR1PtrW0 s1 = pidR1PtrW0 s0 && x4 s1 = x4 s0 && x2 s1 = x2 s0 && xl0 s1 = xl0 s0} @-}
t_pidR0_1 :: State -> State
t_pidR0_1 state@State{..} = state{pidR0Pc = (-1)}

{-@ assume t_pidR0_2 :: s0:{v:State | true} -> {s1:State | pidR1Enabled s1 = pidR1Enabled s0 && x0 s1 = x0 s0 && r1 s1 = r1 s0 && pidR1PcK s1 = pidR1PcK s0 && pidR1NumBlocked s1 = pidR1NumBlocked s0 && pidR0Pc s1 = 2 && pidR1Pc s1 = pidR1Pc s0 && pidR0PtrR0 s1 = pidR0PtrR0 s0 && pidR0PtrW0 s1 = pidR0PtrW0 s0 && pidR1PtrR0 s1 = pidR1PtrR0 s0 && pidR1PtrW0 s1 = pidR1PtrW0 s0 && x4 s1 = x4 s0 && x2 s1 = x2 s0 && xl0 s1 = xl0 s0} @-}
t_pidR0_2 :: State -> State
t_pidR0_2 state@State{..} = state{pidR0Pc = 2}

{-@ assume t_pidR0_3 :: s0:{v:State | true} -> {s1:State | pidR1Enabled s1 = (if (((Map_select (pidR1Pc s0) (xl0 s0)) == 1) && ((Map_select (pidR1PtrR0 s0) (xl0 s0)) == (Map_select (pidR1PtrW0 s0) (xl0 s0)))) then (Set_cup (pidR1Enabled s0) (Set_sng (xl0 s0))) else (pidR1Enabled s0)) && x0 s1 = x0 s0 && r1 s1 = r1 s0 && pidR1PcK s1 = pidR1PcK s0 && pidR1NumBlocked s1 = if (((Map_select (pidR1Pc s0) (xl0 s0)) == 1) && ((Map_select (pidR1PtrR0 s0) (xl0 s0)) == (Map_select (pidR1PtrW0 s0) (xl0 s0)))) then (pidR1NumBlocked s0 - 1) else (pidR1NumBlocked s0) && pidR0Pc s1 = 3 && pidR1Pc s1 = pidR1Pc s0 && pidR0PtrR0 s1 = pidR0PtrR0 s0 && pidR0PtrW0 s1 = pidR0PtrW0 s0 && pidR1PtrR0 s1 = pidR1PtrR0 s0 && pidR1PtrW0 s1 = (Map_store (pidR1PtrW0 s0) (xl0 s0) ((Map_select (pidR1PtrW0 s0) (xl0 s0)) + 1)) && x4 s1 = x4 s0 && x2 s1 = x2 s0 && xl0 s1 = xl0 s0} @-}
t_pidR0_3 :: State -> State
t_pidR0_3 state@State{..}
  = state{pidR1PtrW0 =
            (put pidR1PtrW0 xl0 ((get pidR1PtrW0 xl0) + 1)),
          pidR0Pc = 3,
          pidR1NumBlocked =
            if
              (((get pidR1Pc xl0) == 1) &&
                 ((get pidR1PtrR0 xl0) == (get pidR1PtrW0 xl0)))
              then pidR1NumBlocked - 1 else pidR1NumBlocked}

{-@ assume t_pidR0_4 :: s0:{v:State | true} -> x4_e:(Val Pid) -> {s1:State | pidR1Enabled s1 = pidR1Enabled s0 && x0 s1 = x0 s0 && r1 s1 = r1 s0 && pidR1PcK s1 = pidR1PcK s0 && pidR1NumBlocked s1 = pidR1NumBlocked s0 && pidR0Pc s1 = 4 && pidR1Pc s1 = pidR1Pc s0 && pidR0PtrR0 s1 = pidR0PtrR0 s0 + 1 && pidR0PtrW0 s1 = pidR0PtrW0 s0 && pidR1PtrR0 s1 = pidR1PtrR0 s0 && pidR1PtrW0 s1 = pidR1PtrW0 s0 && x4 s1 = x4_e && x2 s1 = x2 s0 && xl0 s1 = xl0 s0} @-}
t_pidR0_4 :: State -> Val Pid -> State
t_pidR0_4 state@State{..} x4_e
  = state{pidR0PtrR0 = pidR0PtrR0 + 1, pidR0Pc = 4, x4 = x4_e}

{-@ assume t_pidR0_5 :: s0:{v:State | true} -> {s1:State | pidR1Enabled s1 = pidR1Enabled s0 && x0 s1 = x0 s0 && r1 s1 = r1 s0 && pidR1PcK s1 = pidR1PcK s0 && pidR1NumBlocked s1 = pidR1NumBlocked s0 && pidR0Pc s1 = 0 && pidR1Pc s1 = pidR1Pc s0 && pidR0PtrR0 s1 = pidR0PtrR0 s0 && pidR0PtrW0 s1 = pidR0PtrW0 s0 && pidR1PtrR0 s1 = pidR1PtrR0 s0 && pidR1PtrW0 s1 = pidR1PtrW0 s0 && x4 s1 = x4 s0 && x2 s1 = x2 s0 && xl0 s1 = xl0 s0 + 1} @-}
t_pidR0_5 :: State -> State
t_pidR0_5 state@State{..} = state{xl0 = xl0 + 1, pidR0Pc = 0}

{-@ assume t_pidR1_0 :: s0:{v:State | true} -> ir1:Int -> {s1:State | (pidR1Enabled s1 = if ((Map_select (pidR1PtrR0 s0) ir1) == (Map_select (pidR1PtrW0 s0) ir1)) then (Set_dif (pidR1Enabled s0) (Set_sng ir1)) else (pidR1Enabled s0)) && x0 s1 = x0 s0 && r1 s1 = r1 s0 && pidR1PcK s1 = (Map_store (Map_store (pidR1PcK s0) 0 ((Map_select (pidR1PcK s0) 0) - 1)) 1 ((Map_select (pidR1PcK s0) 1) + 1)) && pidR1NumBlocked s1 = if ((Map_select (pidR1PtrR0 s0) ir1) == (Map_select (pidR1PtrW0 s0) ir1)) then (pidR1NumBlocked s0 + 1) else (pidR1NumBlocked s0) && pidR0Pc s1 = pidR0Pc s0 && pidR1Pc s1 = (Map_store (pidR1Pc s0) ir1 1) && pidR0PtrR0 s1 = pidR0PtrR0 s0 && pidR0PtrW0 s1 = pidR0PtrW0 s0 && pidR1PtrR0 s1 = pidR1PtrR0 s0 && pidR1PtrW0 s1 = pidR1PtrW0 s0 && x4 s1 = x4 s0 && x2 s1 = x2 s0 && xl0 s1 = xl0 s0} @-}
t_pidR1_0 :: State -> Int -> State
t_pidR1_0 state@State{..} ir1
  = state{pidR1Pc = (put pidR1Pc ir1 1),
          pidR1PcK =
            (put (put pidR1PcK 0 ((get pidR1PcK 0) - 1)) 1
               ((get pidR1PcK 1) + 1)),
          pidR1NumBlocked =
            if ((get pidR1PtrR0 ir1) == (get pidR1PtrW0 ir1)) then
              pidR1NumBlocked + 1 else pidR1NumBlocked}

{-@ assume t_pidR1_1 :: s0:{v:State | true} -> ir1:Int -> x2_e:(Map_t Int (Val Pid)) -> {s1:State | pidR1Enabled s1 = pidR1Enabled s0 && x0 s1 = x0 s0 && r1 s1 = r1 s0 && pidR1PcK s1 = (Map_store (Map_store (pidR1PcK s0) 1 ((Map_select (pidR1PcK s0) 1) - 1)) 2 ((Map_select (pidR1PcK s0) 2) + 1)) && pidR1NumBlocked s1 = pidR1NumBlocked s0 && pidR0Pc s1 = pidR0Pc s0 && pidR1Pc s1 = (Map_store (pidR1Pc s0) ir1 2) && pidR0PtrR0 s1 = pidR0PtrR0 s0 && pidR0PtrW0 s1 = pidR0PtrW0 s0 && pidR1PtrR0 s1 = (Map_store (pidR1PtrR0 s0) ir1 ((Map_select (pidR1PtrR0 s0) ir1) + 1)) && pidR1PtrW0 s1 = pidR1PtrW0 s0 && x4 s1 = x4 s0 && x2 s1 = x2_e && xl0 s1 = xl0 s0} @-}
t_pidR1_1 :: State -> Int -> Map_t Int (Val Pid) -> State
t_pidR1_1 state@State{..} ir1 x2_e
  = state{pidR1PtrR0 =
            (put pidR1PtrR0 ir1 ((get pidR1PtrR0 ir1) + 1)),
          pidR1Pc = (put pidR1Pc ir1 2),
          pidR1PcK =
            (put (put pidR1PcK 1 ((get pidR1PcK 1) - 1)) 2
               ((get pidR1PcK 2) + 1)),
          x2 = x2_e}

{-@ assume t_pidR1_2 :: s0:{v:State | true} -> ir1:Int -> {s1:State | pidR1Enabled s1 = Set_dif (pidR1Enabled s0) (Set_sng ir1) && x0 s1 = x0 s0 && r1 s1 = r1 s0 && pidR1PcK s1 = (Map_store (Map_store (pidR1PcK s0) 2 ((Map_select (pidR1PcK s0) 2) - 1)) (-1) ((Map_select (pidR1PcK s0) (-1)) + 1)) && pidR1NumBlocked s1 = pidR1NumBlocked s0 && pidR0Pc s1 = pidR0Pc s0 && pidR1Pc s1 = (Map_store (pidR1Pc s0) ir1 (-1)) && pidR0PtrR0 s1 = pidR0PtrR0 s0 && pidR0PtrW0 s1 = pidR0PtrW0 s0 + 1 && pidR1PtrR0 s1 = pidR1PtrR0 s0 && pidR1PtrW0 s1 = pidR1PtrW0 s0 && x4 s1 = x4 s0 && x2 s1 = x2 s0 && xl0 s1 = xl0 s0} @-}
t_pidR1_2 :: State -> Int -> State
t_pidR1_2 state@State{..} ir1
  = state{pidR0PtrW0 = pidR0PtrW0 + 1,
          pidR1Pc = (put pidR1Pc ir1 (-1)),
          pidR1PcK =
            (put (put pidR1PcK 2 ((get pidR1PcK 2) - 1)) (-1)
               ((get pidR1PcK (-1)) + 1))}

{-@ assume t_pidR1_3 :: s0:{v:State | true} -> ir1:Int -> {s1:State | pidR1Enabled s1 = Set_dif (pidR1Enabled s0) (Set_sng ir1) && x0 s1 = x0 s0 && r1 s1 = r1 s0 && pidR1PcK s1 = (Map_store (Map_store (pidR1PcK s0) 2 ((Map_select (pidR1PcK s0) 2) - 1)) (-1) ((Map_select (pidR1PcK s0) (-1)) + 1)) && pidR1NumBlocked s1 = if (((Map_select (pidR1Pc s0) ir1) == 1) && ((Map_select (pidR1PtrR0 s0) ir1) == (Map_select (pidR1PtrW0 s0) ir1))) then (pidR1NumBlocked s0 - 1) else (pidR1NumBlocked s0) && pidR0Pc s1 = pidR0Pc s0 && pidR1Pc s1 = (Map_store (pidR1Pc s0) ir1 (-1)) && pidR0PtrR0 s1 = pidR0PtrR0 s0 && pidR0PtrW0 s1 = pidR0PtrW0 s0 && pidR1PtrR0 s1 = pidR1PtrR0 s0 && pidR1PtrW0 s1 = (Map_store (pidR1PtrW0 s0) ir1 ((Map_select (pidR1PtrW0 s0) ir1) + 1)) && x4 s1 = x4 s0 && x2 s1 = x2 s0 && xl0 s1 = xl0 s0} @-}
t_pidR1_3 :: State -> Int -> State
t_pidR1_3 state@State{..} ir1
  = state{pidR1PtrW0 =
            (put pidR1PtrW0 ir1 ((get pidR1PtrW0 ir1) + 1)),
          pidR1Pc = (put pidR1Pc ir1 (-1)),
          pidR1PcK =
            (put (put pidR1PcK 2 ((get pidR1PcK 2) - 1)) (-1)
               ((get pidR1PcK (-1)) + 1)),
          pidR1NumBlocked =
            if
              (((get pidR1Pc ir1) == 1) &&
                 ((get pidR1PtrR0 ir1) == (get pidR1PtrW0 ir1)))
              then pidR1NumBlocked - 1 else pidR1NumBlocked}



{-@ assume state0 :: {v:State | (pidR0Pc v == 0 && pidR0PtrR0 v == 0 && 0 <= pidR0PtrR0 v && pidR0PtrW0 v == 0 && 0 <= pidR0PtrW0 v && pidR0PtrR0 v <= pidR0PtrW0 v && xl0 v == 0) && (r1 v == Map_select (pidR1PcK v) 0 && ((Map_select (pidR1PcK v) (-1 : int) + Map_select (pidR1PcK v) 0) + Map_select (pidR1PcK v) 1) + Map_select (pidR1PcK v) 2 == r1 v && 0 == Map_select (pidR1PcK v) (-1 : int) && 0 == Map_select (pidR1PcK v) 1 && 0 == Map_select (pidR1PcK v) 2 && 0 <= Map_select (pidR1PcK v) 1 && 0 <= Map_select (pidR1PcK v) 2) && x0 v > 0 && pidR1NumBlocked v == 0 && x0 v == r1 v} @-}

{-@ assume sched0 :: state0:State -> [Pid_pre {v:Int | Set_mem v (pidR1Enabled state0) && Map_select (pidR1Pc state0) v == 0 && (0 <= v && v < r1 state0) && (Map_select (pidR1PtrR0 state0) v <= 0 && 0 <= Map_select (pidR1PtrR0 state0) v) && Map_select (pidR1PtrW0 state0) v == 0 && 0 <= Map_select (pidR1PtrW0 state0) v}] @-}
{-@ data State = State{x0 :: Int, r1 :: Int, pidR1PcK :: Map_t Int Int,
                   pidR1NumBlocked :: Int, pidR0Pc :: Int, pidR1Pc :: Map_t Int Int,
                   pidR0PtrR0 :: Int, pidR0PtrW0 :: Int, pidR1PtrR0 :: Map_t Int Int,
                   pidR1PtrW0 :: Map_t Int Int, x4 :: Val (Pid_pre Int),
                   pidR1Enabled :: Set Int,
                   x2 :: Map_t Int (Val (Pid_pre Int)), xl0 :: Int} @-}

data State = State{x0 :: Int, r1 :: Int, pidR1PcK :: Map_t Int Int,
                   pidR1NumBlocked :: Int, pidR0Pc :: Int, pidR1Pc :: Map_t Int Int,
                   pidR0PtrR0 :: Int, pidR0PtrW0 :: Int, pidR1PtrR0 :: Map_t Int Int,
                   pidR1PtrW0 :: Map_t Int Int, x4 :: Val (Pid_pre Int),
                   pidR1Enabled :: Set Int,
                   x2 :: Map_t Int (Val (Pid_pre Int)), xl0 :: Int}


data Pid_pre p1 = PIDR0
                | PIDR1 p1
                deriving Show
type Pid = Pid_pre Int
isPidR0 PIDR0 = (True)
isPidR0 _ = (False)
isPidR1 (PIDR1 ir1) = (True)
isPidR1 _ = (False)


{-@ measure isPidR0 @-}
{-@ measure isPidR1 @-}
