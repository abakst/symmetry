{-# Language RecordWildCards #-}
module SymVerify () where
import SymVector
import SymMap
import SymBoilerPlate
import Language.Haskell.Liquid.Prelude


state0 :: State
state0 = undefined

sched0 :: State -> [Pid]
sched0 state = undefined

check = runState state0 emptyVec emptyVec2D (sched0 state0)

{-@
runState :: state:{v:State | pidR0PtrW0 v >= 0 && (pidR0Pc v = (-1) => x_loop_0 v = r2 v) && ((pidR0Pc v = 1 || pidR0Pc v = 2 || pidR0Pc v = 3) => x_loop_0 v < r2 v) && (x_loop_0 v <= r2 v) && x_1 v = r2 v && x_loop_0 v >= 0 }
         -> Vec<{\i -> false}, {\x y -> true}> (Val Pid)
         -> Vec2D<{\p i -> 0 <= p && p <= x_loop_0 state && (pidR0Pc state != 3 => p < x_loop_0 state) && 0 <= i && i < Map_select (pidR2PtrW0 state) p },{\p i v -> true}> (Val Pid)
         -> [Pid_pre {v:Int | Map_select (pidR2PtrW0 state) v >= 0 && 0 <= v && v < r2 state &&
                              Map_select (pidR2PtrW0 state) v <= 1 &&
                              ((pidR0Pc state = 3) => ((Map_select (pidR2PtrW0 state) v = 1) <=> v <= x_loop_0 state)) &&
                              ((pidR0Pc state != 3) => ((Map_select (pidR2PtrW0 state) v = 1) <=> v < x_loop_0 state))}]
         -> ()
@-}
runState :: State -> Vec (Val Pid) -> Vec2D (Val Pid) -> [Pid] -> ()
runState state@State{pidR2PtrW0 = pidR2PtrW0,..} pidR0Buf0 pidR2Buf0 (PIDR0 : PIDR2 i : sched)
  | ((pidR0Pc == 0) && (x_loop_0 < x_1)) =
    runState state{pidR0Pc = 1} pidR0Buf0 pidR2Buf0 sched
  | ((pidR0Pc == 0) && (not (x_loop_0 < x_1))) =
    runState state{pidR0Pc = (-1)} pidR0Buf0 pidR2Buf0 sched
  | (pidR0Pc == 1) =
    runState state{pidR0Pc = 2} pidR0Buf0 pidR2Buf0 sched
  | (pidR0Pc == 2) && (i == x_loop_0) =
      {-@ qualif Upd(v:State, w:State): pidR2PtrW0 v = Map_store (pidR2PtrW0 w) (x_loop_0 w) (Map_select (pidR2PtrW0 w) (x_loop_0 w) + 1) @-}
      {-@ qualif MapUpd(v:Map_t Int Int, w:Map_t Int Int, s:State): v = Map_store w (x_loop_0 s) (Map_select w (x_loop_0 s) + 1) @-}
    {-@ qualif PcEq3(v:State): pidR0Pc v = 3 @-}
        runState
          state{ pidR2PtrW0 =
               (put pidR2PtrW0 x_loop_0 ((get pidR2PtrW0 x_loop_0) + 1)),
                pidR0Pc = 3}
          pidR0Buf0
          (setVec2D x_loop_0 (get pidR2PtrW0 x_loop_0) 
                    VUnit pidR2Buf0)
          sched
  | (pidR0Pc == 3) =
    runState state{x_loop_0 = x_loop_0 + 1, pidR0Pc = 0} pidR0Buf0
      pidR2Buf0
      sched
  | (pidR0Pc == (-1)) =
    liquidAssert (x_loop_0 == r2) ()
runState state@State{..} pidR0Buf0 pidR2Buf0 ((PIDR2 ir2) : sched)
  | ((get pidR2Pc ir2) == 0) =
    runState state{pidR2Pc = (put pidR2Pc ir2 (-1))} pidR0Buf0
      pidR2Buf0
      sched
runState state@State{..} pidR0Buf0 pidR2Buf0
  (PIDR0 : ((PIDR2 ir2) : sched))
  = liquidAssert
      (not
         ((False || False) &&
            ((((get pidR2PcK (-1)) == r2 - 1) &&
                (False || ((get pidR2Pc ir2) == (-1))))
               && (False || (pidR0Pc == (-1))))))
      $ ()

{-@ assume state0 :: {v:State | (pidR0Pc v == 0 && pidR0PtrR0 v == 0 && 0 <= pidR0PtrR0 v && pidR0PtrW0 v == 0 && 0 <= pidR0PtrW0 v && pidR0PtrR0 v <= pidR0PtrW0 v) && (r2 v - 1 == Map_select (pidR2PcK v) 0 && 0 == Map_select (pidR2Pc v) (pidR2K v) && (0 <= pidR2K v && pidR2K v < r2 v) && Map_select (pidR2PcK v) (-1 : int) + Map_select (pidR2PcK v) 0 == r2 v - 1 && 0 == Map_select (pidR2PcK v) (-1 : int)) && x_loop_0 v == 0 && x_1 v == r2 v} @-}
{-@ assume sched0 :: state0:State -> [Pid_pre {v:Int | Map_select (pidR2Pc state0) v == 0 && (0 <= v && v < r2 state0) && (Map_select (pidR2PtrR0 state0) v <= 0 && 0 <= Map_select (pidR2PtrW0 state0) v) && Map_select (pidR2PtrW0 state0) v == 0 && 0 <= Map_select (pidR2PtrW0 state0) v}] @-}
{-@ data State = State{pidR0Pc :: Int, pidR2Pc :: Map_t Int Int,
                   pidR0PtrR0 :: Int, pidR2PtrR0 :: Map_t Int {v:Int | v >= 0}, pidR0PtrW0 :: Int,
                   pidR2PtrW0 :: Map_t Int {v:Int | v >= 0}, x_loop_0 :: Int, r2 :: Int,
                   pidR2PcK :: Map_t Int Int, pidR2K :: Int, x_1 :: Int} @-}

{-@ qualif Deref_pidR0Pc(v:Int, w:State): v = pidR0Pc w @-}
{-@ qualif Eq_pidR0Pc(v:State, w:State ): pidR0Pc v = pidR0Pc w @-}
{-@ qualif Deref_pidR2Pc(v:Map_t Int Int, w:State): v = pidR2Pc w @-}
{-@ qualif Eq_pidR2Pc(v:State, w:State ): pidR2Pc v = pidR2Pc w @-}
{-@ qualif Deref_pidR0PtrR0(v:Int, w:State): v = pidR0PtrR0 w @-}
{-@ qualif Eq_pidR0PtrR0(v:State, w:State ): pidR0PtrR0 v = pidR0PtrR0 w @-}
{-@ qualif Deref_pidR2PtrR0(v:Map_t Int Int, w:State): v = pidR2PtrR0 w @-}
{-@ qualif Eq_pidR2PtrR0(v:State, w:State ): pidR2PtrR0 v = pidR2PtrR0 w @-}
{-@ qualif Deref_pidR0PtrW0(v:Int, w:State): v = pidR0PtrW0 w @-}
{-@ qualif Eq_pidR0PtrW0(v:State, w:State ): pidR0PtrW0 v = pidR0PtrW0 w @-}
{-@ qualif Deref_pidR2PtrW0(v:Map_t Int Int, w:State): v = pidR2PtrW0 w @-}
{-@ qualif Eq_pidR2PtrW0(v:State, w:State ): pidR2PtrW0 v = pidR2PtrW0 w @-}
{-@ qualif Deref_x_loop_0(v:Int, w:State): v = x_loop_0 w @-}
{-@ qualif Eq_x_loop_0(v:State, w:State ): x_loop_0 v = x_loop_0 w @-}
{-@ qualif Deref_r2(v:Int, w:State): v = r2 w @-}
{-@ qualif Eq_r2(v:State, w:State ): r2 v = r2 w @-}
{-@ qualif Deref_pidR2PcK(v:Map_t Int Int, w:State): v = pidR2PcK w @-}
{-@ qualif Eq_pidR2PcK(v:State, w:State ): pidR2PcK v = pidR2PcK w @-}
{-@ qualif Deref_pidR2K(v:Int, w:State): v = pidR2K w @-}
{-@ qualif Eq_pidR2K(v:State, w:State ): pidR2K v = pidR2K w @-}
{-@ qualif Deref_x_1(v:Int, w:State): v = x_1 w @-}
{-@ qualif Eq_x_1(v:State, w:State ): x_1 v = x_1 w @-}



data State = State{pidR0Pc :: Int, pidR2Pc :: Map_t Int Int,
                   pidR0PtrR0 :: Int, pidR2PtrR0 :: Map_t Int Int, pidR0PtrW0 :: Int,
                   pidR2PtrW0 :: Map_t Int Int, x_loop_0 :: Int, r2 :: Int,
                   pidR2PcK :: Map_t Int Int, pidR2K :: Int, x_1 :: Int}


data Pid_pre p1 = PIDR0
                | PIDR2 p1
type Pid = Pid_pre Int
isPidR0 PIDR0 = (True)
isPidR0 _ = (False)
isPidR2 (PIDR2 ir2) = (True)
isPidR2 _ = (False)


{-@ measure isPidR0 @-}
{-@ measure isPidR2 @-}

{-@ qualif IterInv(v:State): pidR0Pc v == -1 => x_loop_0 v == r2 v @-}
{-@ qualif IterInv(v:State): x_loop_0 v <= r2 v @-}
{-@ qualif Iter(v:State): pidR0Pc v == 1 => x_loop_0 v < r2 v @-}
{-@ qualif Iter(v:State): pidR0Pc v == 2 => x_loop_0 v < r2 v @-}
{-@ qualif Iter(v:State): pidR0Pc v == 3 => x_loop_0 v < r2 v @-}


