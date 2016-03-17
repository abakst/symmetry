{-# Language RecordWildCards #-}
module SymVerify () where
import SymVector
import SymMap
import SymBoilerPlate
import Data.Set
import Language.Haskell.Liquid.Prelude


state0 :: State
state0 = undefined

sched0 :: State -> [Pid]
sched0 state = undefined

check = runState state0 emptyVec emptyVec2D (sched0 state0)
{-@ 
predicate StatePre V = (0 <= xl0 V && xl0 V <= r1 V && r1 V > 0) &&
                       (0 <= xl1 V && xl1 V <= r1 V) &&

                       (((2 <= pidR0Pc V && pidR0Pc V <= 4) => (xl0 V < r1 V))) &&
                       (pidR0Pc V = (-1) => (xl0 V = r1 V)) &&
                       (pidR0Pc V > 4    => (xl0 V = r1 V)) &&

                       (((0 <= pidR0Pc V && pidR0Pc V <= 4) => (xl1 V == 0))) &&
                       ((5 < pidR0Pc V  && pidR0Pc V <= 8) => (xl1 V < r1 V)) &&
                       (pidR0Pc V = (-1) => (xl1 V = r1 V)) &&

                       (pidR0PtrR0 V <= pidR0PtrW0 V) &&
                       (0 <= pidR0PtrR0 V) &&
                       (pidR1NumBlocked V >= 0) &&
 
                       (if (pidR0Pc V = 8) then (pidR0PtrR0 V = xl1 V + 1) else (pidR0PtrR0 V = xl1 V)) &&
                       (pidR0PtrW0 V = Map_select (pidR1PcK V) (-1)) &&
                       (pidR0PtrR0 V = xl1 V + (if (pidR0Pc V = 8) then 1 else 0))
@-}

{-@ predicate Blocked S I = (Map_select (pidR1Pc S) I = 1 && Map_select (pidR1PtrW0 S) I <= Map_select (pidR1PtrR0 S) I) @-}

{-@ 
predicate Multi S V = (0 <= V && V < r1 S) &&
                      (Map_select (pidR1PtrR0 S) V = (if (Map_select (pidR1Pc S) V > 1 || Map_select (pidR1Pc S) V == (-1)) then 1 else 0)) &&
                      ((Map_select (pidR1PtrW0 S) V = 0 => (Map_select (pidR1Pc S) V = 0 || Map_select (pidR1Pc S) V = 1))) &&
                      (((Map_select (pidR1PtrW0 S) V = (if (V < xl0 S || (V == xl0 S && pidR0Pc S = 4)) then 1 else 0)))) &&
                      ((Map_select (pidR1Pc S) V = 2 => isPidR0 (vPid (Map_select (x2 S) V))))
@-}
                      -- (Set_mem V (pidR1Blocked S) <=>
                      --   ((Map_select (pidR1Pc S) V = 1) && (V >= xl0 S && (V != xl0 S || pidR0Pc S != 4)))) && 

{-@ data State = State{x0 :: Int, r1 :: Int, pidR1PcK :: Map_t Int Int,
                   pidR1Blocked :: Set Int,
                   pidR1NumBlocked :: Int, pidR0Pc :: Int, pidR1Pc :: Map_t Int Int,
                   pidR0PtrR0 :: Int, pidR0PtrW0 :: Int, pidR1PtrR0 :: Map_t Int Int,
                   pidR1PtrW0 :: Map_t Int Int, x4 :: Val (Pid_pre Int),
                   x2 :: Map_t Int (Val (Pid_pre Int)), xl0 :: Int, xl1 :: Int} @-}

{-@
runState :: state:{v:State | StatePre v }
         -> Vec <\i -> {v:Val Pid | isPidR1 (vPid v)}> (Val Pid)
         -> Vec2D <\i j -> {v:Val Pid | isPidR0 (vPid v) }>(Val Pid)
         -> [Pid_pre {v:Int | Multi state v} ]
         -> ()
@-}
runState :: State -> Vec (Val Pid) -> Vec2D (Val Pid) -> [Pid] -> ()
runState state@State{..} pidR0Buf0 pidR1Buf0 (PIDR0 : PIDR1 i : sched)
  | (pidR0Pc == 0) =
    runState (tx0_0 state) pidR0Buf0 pidR1Buf0 sched
  | ((pidR0Pc == 1) && (xl0 < r1)) =
    runState (tx0_1 state) pidR0Buf0 pidR1Buf0 sched
  | ((pidR0Pc == 1) && (not (xl0 < r1))) =
    runState (tx0_1 state) pidR0Buf0 pidR1Buf0 sched
  | (pidR0Pc == 2) =
    runState (tx0_2 state) pidR0Buf0 pidR1Buf0 sched
  | (pidR0Pc == 3 && xl0 == i) =
    runState (tx0_3 state) pidR0Buf0
        (setVec2D xl0 (get pidR1PtrW0 xl0) (VPid PIDR0) pidR1Buf0)
        sched
  | (pidR0Pc == 4) =
    runState (tx0_4 state)  pidR0Buf0 pidR1Buf0 sched
  | ((pidR0Pc == 5) && (xl1 < r1)) =
    runState (tx0_5 state) pidR0Buf0 pidR1Buf0 sched
  | ((pidR0Pc == 5) && (not (xl1 < r1))) =
    runState (tx0_5 state) pidR0Buf0 pidR1Buf0 sched
  | (pidR0Pc == 6) =
    runState (tx0_6 state) pidR0Buf0 pidR1Buf0 sched
  | ((pidR0Pc == 7) && (pidR0PtrR0 < pidR0PtrW0)) =
    runState (tx0_7 state) pidR0Buf0 pidR1Buf0 sched
  | (pidR0Pc == 8) =
    runState (tx0_8 state) pidR0Buf0 pidR1Buf0 sched
runState state@State{..} pidR0Buf0 pidR1Buf0 ((PIDR1 ir1) : sched)
  | ((get pidR1Pc ir1) == 0 && get pidR1PcK 0 > 0) =
    runState (tx1_0 state ir1) pidR0Buf0 pidR1Buf0 sched
  | (((get pidR1Pc ir1) == 1) &&
     (get pidR1PtrR0 ir1 < get pidR1PtrW0 ir1) &&
    not (member ir1 pidR1Blocked)) =
      runState (tx1_1 state ir1 (getVec2D ir1 (get pidR1PtrR0 ir1) pidR1Buf0)) pidR0Buf0 pidR1Buf0 sched
  | ((get pidR1Pc ir1) == 2) =
    case (get x2 ir1) of
        VPid PIDR0 -> runState (tx1_2 state ir1) (setVec pidR0PtrW0 (VPid (PIDR1 ir1)) pidR0Buf0)
                          pidR1Buf0
                          sched
        VPid (PIDR1 ir1') -> runState (tx1_2 state ir1) pidR0Buf0
                                (setVec2D ir1' (get pidR1PtrW0 ir1') (VPid (PIDR1 ir1')) pidR1Buf0)
                                sched
runState state@State{..} pidR0Buf0 pidR1Buf0 [PIDR0, PIDR1 i, PIDR1 i']
   = liquidAssert (not (assumption state i i') || get pidR1Pc i == (-1)) $
     liquidAssert (not (assumption state i i') || pidR0Pc == -1) $
                    ()
runState state a0 a1 (s : sched) = runState state a0 a1 sched
                                   
{-@ predicate BlockedDoneP0 S   = (pidR0Pc S = (-1) || (pidR0Pc S = 7 && pidR0PtrW0 S <= pidR0PtrR0 S)) @-}
{-@ predicate BlockedDoneP1 S I J = (Map_select (pidR1PcK S) (-1) + pidR1NumBlocked S == r1 S) &&
                                    (pidR1NumBlocked S = Map_select (pidR1PcK S) 1) &&
                                    (pidR1NumBlocked S >= 0 && Map_select (pidR1PcK S) (-1) >= 0) &&
                                    ((Map_select (pidR1Pc S) I = (-1) && Map_select (pidR1PcK s) (-1) = r1 S) ||
                                     (Map_select (pidR1Pc S) J = 1 && Map_select (pidR1PtrW0 S) J <= Map_select (pidR1PtrR0 S) J && pidR1NumBlocked S > 0 && Map_select (pidR1PcK S) 1 > 0)) @-}

{-@ assume assumption :: s:State -> i:Int -> j:Int ->
                        {v:Bool | (Prop(v) <=>  ((BlockedDoneP0 s) &&
                                                 (BlockedDoneP1 s i j))) }
@-}
assumption :: State -> Int -> Int -> Bool
assumption = undefined

-- axiom: (forall x. x \notin S) <=> emp(S)                                   


-- (\exists x. (~(Blocked) && ~(Done))) \/ (~ (Blocked(P0) \/ forall x. (Done(x))                                   
-- (~ \forall x. (Blocked || Done)) \/ forall x. (Done(x))
-- \forall x. (Blocked(x) \/ Done(x)) ==> forall x. (Done(x))

{-@ assume state0 :: {v:State | (pidR0Pc v == 0 && pidR0PtrR0 v == 0 && 0 <= pidR0PtrR0 v && pidR0PtrW0 v == 0 && 0 <= pidR0PtrW0 v && pidR0PtrR0 v <= pidR0PtrW0 v && xl0 v == 0 && xl1 v == 0) && (r1 v == Map_select (pidR1PcK v) 0 && ((Map_select (pidR1PcK v) (-1 : int) + Map_select (pidR1PcK v) 0) + Map_select (pidR1PcK v) 1) + Map_select (pidR1PcK v) 2 == r1 v && 0 == Map_select (pidR1PcK v) (-1 : int) && 0 == Map_select (pidR1PcK v) 1 && 0 == Map_select (pidR1PcK v) 2 && 0 <= Map_select (pidR1PcK v) 1 && 0 <= Map_select (pidR1PcK v) 2) && x0 v > 0 && pidR1NumBlocked v == 0 && x0 v == r1 v && Set_emp (pidR1Blocked v)} @-}
{-@ assume sched0 :: state0:State -> [Pid_pre {v:Int | (~(Set_mem v (pidR1Blocked state0))) && Map_select (pidR1Pc state0) v == 0 && (0 <= v && v < r1 state0) && (Map_select (pidR1PtrR0 state0) v <= 0 && 0 <= Map_select (pidR1PtrR0 state0) v) && Map_select (pidR1PtrW0 state0) v == 0 && 0 <= Map_select (pidR1PtrW0 state0) v}] @-}
{-@ data State = State{x0 :: Int, r1 :: Int, pidR1PcK :: Map_t Int Int,
                   pidR1Blocked :: Set Int,
                   pidR1NumBlocked :: Int, pidR0Pc :: Int, pidR1Pc :: Map_t Int Int,
                   pidR0PtrR0 :: Int, pidR0PtrW0 :: Int, pidR1PtrR0 :: Map_t Int Int,
                   pidR1PtrW0 :: Map_t Int Int, x4 :: Val (Pid_pre Int),
                   x2 :: Map_t Int (Val (Pid_pre Int)), xl0 :: Int, xl1 :: Int} @-}



data State = State{x0 :: Int, r1 :: Int, pidR1PcK :: Map_t Int Int,
                   pidR1Blocked :: Set Int,
                   pidR1NumBlocked :: Int, pidR0Pc :: Int, pidR1Pc :: Map_t Int Int,
                   pidR0PtrR0 :: Int, pidR0PtrW0 :: Int, pidR1PtrR0 :: Map_t Int Int,
                   pidR1PtrW0 :: Map_t Int Int, x4 :: Val (Pid_pre Int),
                   x2 :: Map_t Int (Val (Pid_pre Int)), xl0 :: Int, xl1 :: Int}


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

{-@ assume tx0_0 :: s0:State -> {v:State | x0 v = x0 s0 && 
                                         r1 v = r1 s0 && 
                                         pidR1PcK v = pidR1PcK s0 &&
                                         pidR1Blocked v = pidR1Blocked s0 &&
                                         pidR1NumBlocked v = pidR1NumBlocked s0 &&
                                         pidR0Pc v = 1 &&
                                         pidR1Pc v = pidR1Pc s0 &&
                                         pidR0PtrR0 v = pidR0PtrR0 s0 &&
                                         pidR0PtrW0 v = pidR0PtrW0 s0 &&
                                         pidR1PtrR0 v = pidR1PtrR0 s0 &&
                                         pidR1PtrW0 v = pidR1PtrW0 s0 &&
                                         x4 v = x4 s0 &&
                                         x2 v = x2 s0 &&
                                         xl0 v = xl0 s0 &&
                                         xl1 v = xl1 s0 }
@-}
tx0_0 :: State -> State
tx0_0 = undefined
{-@ assume tx0_1 :: s0:State -> {v:State | x0 v = x0 s0 && 
                                         r1 v = r1 s0 && 
                                         pidR1PcK v = pidR1PcK s0 &&
                                         pidR1Blocked v = pidR1Blocked s0 &&
                                         pidR1NumBlocked v = pidR1NumBlocked s0 &&
                                         pidR0Pc v = (if (xl0 s0 < r1 s0) then 2 else 5) &&
                                         pidR1Pc v = pidR1Pc s0 &&
                                         pidR0PtrR0 v = pidR0PtrR0 s0 &&
                                         pidR0PtrW0 v = pidR0PtrW0 s0 &&
                                         pidR1PtrR0 v = pidR1PtrR0 s0 &&
                                         pidR1PtrW0 v = pidR1PtrW0 s0 &&
                                         x4 v = x4 s0 &&
                                         x2 v = x2 s0 &&
                                         xl0 v = xl0 s0 &&
                                         xl1 v = xl1 s0 }
@-}
tx0_1 :: State -> State
tx0_1 = undefined
{-@ assume tx0_2 :: s0:State -> {v:State | x0 v = x0 s0 && 
                                         r1 v = r1 s0 && 
                                         pidR1PcK v = pidR1PcK s0 &&
                                         pidR1Blocked v = pidR1Blocked s0 &&
                                         pidR1NumBlocked v = pidR1NumBlocked s0 &&
                                         pidR0Pc v = 3 &&
                                         pidR1Pc v = pidR1Pc s0 &&
                                         pidR0PtrR0 v = pidR0PtrR0 s0 &&
                                         pidR0PtrW0 v = pidR0PtrW0 s0 &&
                                         pidR1PtrR0 v = pidR1PtrR0 s0 &&
                                         pidR1PtrW0 v = pidR1PtrW0 s0 &&
                                         x4 v = x4 s0 &&
                                         x2 v = x2 s0 &&
                                         xl0 v = xl0 s0 &&
                                         xl1 v = xl1 s0 }
@-}
tx0_2 :: State -> State
tx0_2 = undefined

                                         -- pidR1NumBlocked v = pidR1NumBlocked s0 - (if (Map_select (pidR1Pc s0) (xl0 s0) == 1 && (Map_select (pidR1PtrR0 s0) (xl0 s0) == Map_select (pidR1PtrW0 s0) (xl0 s0))) then 1 else 0) &&
{-@ assume tx0_3 :: s0:State -> {v:State | x0 v = x0 s0 && 
                                         r1 v = r1 s0 && 
                                         pidR1PcK v = pidR1PcK s0 &&
                                         pidR1Blocked v = Set_dif (pidR1Blocked s0) (Set_sng (xl0 s0)) &&
                                         pidR0Pc v = 4 &&
                                         pidR1NumBlocked v = pidR1NumBlocked s0 - (if (Blocked v (xl0 s0)) then 1 else 0) &&
                                         pidR1Pc v = pidR1Pc s0 &&
                                         pidR0PtrR0 v = pidR0PtrR0 s0 &&
                                         pidR0PtrW0 v = pidR0PtrW0 s0 &&
                                         pidR1PtrR0 v = pidR1PtrR0 s0 &&
                                         pidR1PtrW0 v = Map_store (pidR1PtrW0 s0) (xl0 s0) (Map_select (pidR1PtrW0 s0) (xl0 s0) + 1) &&
                                         x4 v = x4 s0 &&
                                         x2 v = x2 s0 &&
                                         xl0 v = xl0 s0 &&
                                         xl1 v = xl1 s0 }
@-}
tx0_3 :: State -> State
tx0_3 = undefined

{-@ assume tx0_4 :: s0:State -> {v:State | x0 v = x0 s0 && 
                                           r1 v = r1 s0 && 
                                           pidR1PcK v = pidR1PcK s0 &&
                                           pidR1Blocked v = pidR1Blocked s0 &&
                                           pidR1NumBlocked v = pidR1NumBlocked s0 &&
                                           pidR0Pc v = 1 &&
                                           pidR1Pc v = pidR1Pc s0 &&
                                           pidR0PtrR0 v = pidR0PtrR0 s0 &&
                                           pidR0PtrW0 v = pidR0PtrW0 s0 &&
                                           pidR1PtrR0 v = pidR1PtrR0 s0 &&
                                           pidR1PtrW0 v = pidR1PtrW0 s0 &&
                                           x4 v = x4 s0 &&
                                           x2 v = x2 s0 &&
                                           xl0 v = xl0 s0 + 1 &&
                                           xl1 v = xl1 s0 }
@-}
tx0_4 :: State -> State
tx0_4 = undefined

{-@ assume tx0_5 :: s0:State -> {v:State | x0 v = x0 s0 && 
                                           r1 v = r1 s0 && 
                                           pidR1PcK v = pidR1PcK s0 &&
                                           pidR1Blocked v = pidR1Blocked s0 &&
                                           pidR1NumBlocked v = pidR1NumBlocked s0 &&
                                           pidR0Pc v = (if (xl1 s0 < r1 s0) then 6 else (-1)) &&
                                           pidR1Pc v = pidR1Pc s0 &&
                                           pidR0PtrR0 v = pidR0PtrR0 s0 &&
                                           pidR0PtrW0 v = pidR0PtrW0 s0 &&
                                           pidR1PtrR0 v = pidR1PtrR0 s0 &&
                                           pidR1PtrW0 v = pidR1PtrW0 s0 &&
                                           x4 v = x4 s0 &&
                                           x2 v = x2 s0 &&
                                           xl0 v = xl0 s0 &&
                                           xl1 v = xl1 s0 }
@-}
tx0_5 :: State -> State
tx0_5 = undefined
{-@ assume tx0_6 :: s0:State -> {v:State | x0 v = x0 s0 && 
                                           r1 v = r1 s0 && 
                                           pidR1PcK v = pidR1PcK s0 &&
                                           pidR1Blocked v = pidR1Blocked s0 &&
                                           pidR1NumBlocked v = pidR1NumBlocked s0 &&
                                           pidR0Pc v = 7 &&
                                           pidR1Pc v = pidR1Pc s0 &&
                                           pidR0PtrR0 v = pidR0PtrR0 s0 &&
                                           pidR0PtrW0 v = pidR0PtrW0 s0 &&
                                           pidR1PtrR0 v = pidR1PtrR0 s0 &&
                                           pidR1PtrW0 v = pidR1PtrW0 s0 &&
                                           x4 v = x4 s0 &&
                                           x2 v = x2 s0 &&
                                           xl0 v = xl0 s0 &&
                                           xl1 v = xl1 s0 }
@-}
tx0_6 :: State -> State
tx0_6 = undefined
{-@ assume tx0_7 :: s0:State -> {v:State | x0 v = x0 s0 && 
                                           r1 v = r1 s0 && 
                                           pidR1PcK v = pidR1PcK s0 &&
                                           pidR1Blocked v = pidR1Blocked s0 &&
                                           pidR1NumBlocked v = pidR1NumBlocked s0 &&
                                           pidR0Pc v = 8 &&
                                           pidR1Pc v = pidR1Pc s0 &&
                                           pidR0PtrR0 v = pidR0PtrR0 s0 + 1 &&
                                           pidR0PtrW0 v = pidR0PtrW0 s0 &&
                                           pidR1PtrR0 v = pidR1PtrR0 s0 &&
                                           pidR1PtrW0 v = pidR1PtrW0 s0 &&
                                           x4 v = x4 s0 &&
                                           x2 v = x2 s0 &&
                                           xl0 v = xl0 s0 &&
                                           xl1 v = xl1 s0 }
@-}
tx0_7 :: State -> State
tx0_7 = undefined
{-@ assume tx0_8 :: s0:State -> {v:State | x0 v = x0 s0 && 
                                           r1 v = r1 s0 && 
                                           pidR1PcK v = pidR1PcK s0 &&
                                           pidR1Blocked v = pidR1Blocked s0 &&
                                           pidR1NumBlocked v = pidR1NumBlocked s0 &&
                                           pidR0Pc v = 5 &&
                                           pidR1Pc v = pidR1Pc s0 &&
                                           pidR0PtrR0 v = pidR0PtrR0 s0 &&
                                           pidR0PtrW0 v = pidR0PtrW0 s0 &&
                                           pidR1PtrR0 v = pidR1PtrR0 s0 &&
                                           pidR1PtrW0 v = pidR1PtrW0 s0 &&
                                           x4 v = x4 s0 &&
                                           x2 v = x2 s0 &&
                                           xl0 v = xl0 s0 &&
                                           xl1 v = xl1 s0 + 1 }
@-}
tx0_8 :: State -> State
tx0_8 = undefined

{-@ assume tx1_0 :: s0:State -> i:Int -> {v:State | x0 v = x0 s0 && 
                                           r1 v = r1 s0 && 
                                           pidR1PcK v = Map_store (Map_store (pidR1PcK s0) 0 (Map_select (pidR1PcK s0) 0 - 1)) 
                                                        1 (Map_select (pidR1PcK s0) 1 + 1) &&
                                           pidR1Blocked v = (if (Map_select (pidR1PtrR0 s0) i = Map_select (pidR1PtrW0 s0) i) then
                                                              (Set_cup (pidR1Blocked s0) (Set_sng i)) else (pidR1Blocked s0)) &&
                                           pidR1NumBlocked v = (if (Map_select (pidR1PtrR0 s0) i = Map_select (pidR1PtrW0 s0) i) then
                                                              (pidR1NumBlocked s0 + 1) else (pidR1NumBlocked s0)) &&
                                           pidR0Pc v = pidR0Pc s0 &&
                                           pidR1Pc v = Map_store (pidR1Pc s0) i 1 &&
                                           pidR0PtrR0 v = pidR0PtrR0 s0 &&
                                           pidR0PtrW0 v = pidR0PtrW0 s0 &&
                                           pidR1PtrR0 v = pidR1PtrR0 s0 &&
                                           pidR1PtrW0 v = pidR1PtrW0 s0 &&
                                           x4 v = x4 s0 &&
                                           x2 v = x2 s0 &&
                                           xl0 v = xl0 s0 &&
                                           xl1 v = xl1 s0  }
@-}
tx1_0 :: State -> Int -> State
tx1_0 = undefined

{-@ assume tx1_1 :: s0:State -> i:Int -> z:Val Pid -> {v:State | x0 v = x0 s0 && 
                                                             r1 v = r1 s0 && 
                                                             pidR1PcK v = Map_store (Map_store (pidR1PcK s0) 1 (Map_select (pidR1PcK s0) 1 - 1)) 
                                                                          2 (Map_select (pidR1PcK s0) 2 + 1) &&
                                                             pidR1Blocked v = pidR1Blocked s0 &&
                                                             pidR1NumBlocked v = pidR1NumBlocked s0 &&
                                                             pidR0Pc v = pidR0Pc s0 &&
                                                             pidR1Pc v = Map_store (pidR1Pc s0) i 2 &&
                                                             pidR0PtrR0 v = pidR0PtrR0 s0 &&
                                                             pidR0PtrW0 v = pidR0PtrW0 s0 &&
                                                             pidR1PtrR0 v = Map_store (pidR1PtrR0 s0) i (Map_select (pidR1PtrR0 s0) i + 1) &&
                                                             pidR1PtrW0 v = pidR1PtrW0 s0 &&
                                                             x4 v = x4 s0 &&
                                                             x2 v = Map_store (x2 s0) i z &&
                                                             xl0 v = xl0 s0 &&
                                                             xl1 v = xl1 s0  }
@-}
tx1_1 :: State -> Int -> Val Pid -> State
tx1_1 = undefined

{-@ assume tx1_2 :: s0:State -> i:Int -> {v:State | x0 v = x0 s0 && 
                                                    r1 v = r1 s0 && 
                                                    pidR1PcK v = Map_store (Map_store (pidR1PcK s0) 2 (Map_select (pidR1PcK s0) 2 - 1)) 
                                                                 (-1) (Map_select (pidR1PcK s0) (-1) + 1) &&
                                                    pidR1Blocked v = pidR1Blocked s0 &&
                                                    pidR1NumBlocked v = pidR1NumBlocked s0 &&
                                                    pidR0Pc v = pidR0Pc s0 &&
                                                    pidR1Pc v = Map_store (pidR1Pc s0) i (-1) &&
                                                    pidR0PtrR0 v = pidR0PtrR0 s0 &&
                                                    pidR0PtrW0 v = pidR0PtrW0 s0 + 1 &&
                                                    pidR1PtrR0 v = pidR1PtrR0 s0 &&
                                                    pidR1PtrW0 v = pidR1PtrW0 s0 &&
                                                    x4 v = x4 s0 &&
                                                    x2 v = x2 s0 &&
                                                    xl0 v = xl0 s0 &&
                                                    xl1 v = xl1 s0  }
@-}
tx1_2 :: State -> Int -> State
tx1_2 = undefined
