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

{-@ initVec2D :: forall <r :: Int -> Int -> Val Pid -> Prop>. s:State -> Vec2D <{\i j -> 0 <= i && i < r2 s && 0 <= j && j < Map_select (pidR2PtrW0 s) i},r> (Val Pid) @-}
initVec2D :: State -> Vec2D (Val Pid)               
initVec2D = undefined

check = 
  let sched = sched0 state0 in
  runState state0 emptyVec (initVec2D state0) sched

{-@ runState :: s:{v:State | 0 <= x_l0 v && x_l0 v < r2 v}
             -> Vec <{\i -> 0 <= i && i < pidR0PtrW0 s},{\i v -> true}> (Val Pid)
             -> Vec2D <{\p i -> 0 <= p && p < r2 s && 0 <= i && i < Map_select (pidR2PtrW0 s) p},{\i j v -> true}> (Val Pid)
             -> [Pid_pre {v:Int | 0 <= v && v < r2 s && Map_select (pidR2PtrW0 s) v >= 0}]
             -> ()
@-}         
runState :: State -> Vec (Val Pid) -> Vec2D (Val Pid) -> [Pid] -> ()
runState state@State{..} pidR0Buf0 pidR2Buf0  (PIDR0 : sched)
  | (pidR0Pc == 0) =
    runState state{pidR0Pc = 1} pidR0Buf0 pidR2Buf0 sched
  | ((pidR0Pc == 1) && (x_l0 < x_1)) =
    runState state{pidR0Pc = 5} pidR0Buf0 pidR2Buf0 sched
  | ((pidR0Pc == 1) && (not (x_l0 < x_1))) =
    runState state{pidR0Pc = 2} pidR0Buf0 pidR2Buf0 sched
  | (pidR0Pc == 2) =
    runState state{pidR0Pc = 3} pidR0Buf0 pidR2Buf0 sched
  | (pidR0Pc == 3) = 
      runState
        state{pidR2PtrW0 =
                (put pidR2PtrW0 x_l0 (get pidR2PtrW0 x_l0 + 1)),
              pidR0Pc = 4}
        pidR0Buf0
        (setVec2D x_l0 (get pidR2PtrW0 x_l0) (VUnit) pidR2Buf0)
        sched

{-@ qualif Foo(v:State, w:State, x:Int): (pidR2PtrW0 v) = Map_store (pidR2PtrW0 w) x (Map_select (pidR2PtrW0 w) x + 1) @-}
{-@ qualif Foo(v:Map_t Int Int, w:Map_t Int Int, x:Int): v = Map_store w x ((Map_select w x) + 1) @-}
  -- | (pidR0Pc == 4) =
  --   runState state{x_l0 = x_l0 + 1, pidR0Pc = 1} pidR0Buf0 pidR2Buf0
  --     sched
  -- | (pidR0Pc == 5) =
  --   liquidAssert (x_l0 == x_1)
  --     (runState state{pidR0Pc = (-1)} pidR0Buf0 pidR2Buf0 sched)
-- runState state@State{..} pidR0Buf0 pidR2Buf0 ((PIDR2 ir2) : sched)
--   | (((get pidR2Pc ir2) == 0) &&
--        ((get pidR2PtrR0 ir2) < (get pidR2PtrW0 ir2)))
--     =
--     runState
--       state{pidR2PtrR0 = (put pidR2PtrR0 ir2 ((get pidR2PtrR0 ir2) + 1)),
--             x_4 = (put x_4 ir2 (getVec2D ir2 (get pidR2PtrR0 ir2) pidR2Buf0)),
--             pidR2Pc = (put pidR2Pc ir2 (-1))}
--       pidR0Buf0
--       pidR2Buf0
--       sched
{- runState state@State{..} pidR0Buf0 pidR2Buf0
  (PIDR0 : ((PIDR2 ir2) : sched))
  = liquidAssert
      (not
         (((((get pidR2PtrW0 ir2) <= (get pidR2PtrR0 ir2)) &&
              ((get pidR2Pc ir2) == 0))
             || False)
            &&
            ((((get pidR2PcK (-1)) + (get pidR2PcK 0) == r2 - 1) &&
                ((((get pidR2PtrW0 ir2) <= (get pidR2PtrR0 ir2)) &&
                    ((get pidR2Pc ir2) == 0))
                   || ((get pidR2Pc ir2) == (-1))))
               && (False || (pidR0Pc == (-1))))))
      () -}

{-@ assume state0 :: {v:State | (pidR0Pc v == 1 && pidR0PtrR0 v == 0 && 0 <= pidR0PtrR0 v && pidR0PtrW0 v == 0 && 0 <= pidR0PtrW0 v && pidR0PtrR0 v <= pidR0PtrW0 v) && (r2 v - 1 == Map_select (pidR2PcK v) 0 && 0 == Map_select (pidR2Pc v) (pidR2K v) && (0 <= pidR2K v && pidR2K v < r2 v) && Map_select (pidR2PcK v) (-1 : int) + Map_select (pidR2PcK v) 0 == r2 v - 1 && 0 == Map_select (pidR2PcK v) (-1 : int)) && x_l0 v == 0} @-}
{-@ assume sched0 :: state0:State -> [Pid_pre {v:Int | Map_select (pidR2Pc state0) v == 0 && (0 <= v && v < r2 state0) && (Map_select (pidR2PtrR0 state0) v <= 0 && 0 <= Map_select (pidR2PtrW0 state0) v) && Map_select (pidR2PtrW0 state0) v == 0 && 0 <= Map_select (pidR2PtrW0 state0) v}] @-}
{-@ data State = State{pidR0Pc :: Int, pidR2Pc :: Map_t Int Int,
                   pidR0PtrR0 :: Int, pidR2PtrR0 :: Map_t Int {v:Int | v >= 0}, pidR0PtrW0 :: Int,
                   pidR2PtrW0 :: Map_t Int {v:Int | v >= 0}, x_4 :: Map_t Int (Val (Pid_pre Int)),
                   x_l0 :: Int, r2 :: Int, pidR2PcK :: Map_t Int Int, pidR2K :: Int,
                   x_1 :: Int} @-}

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
{-@ qualif Deref_x_4(v:Map_t Int (Val (Pid_pre Int)), w:State): v = x_4 w @-}
{-@ qualif Eq_x_4(v:State, w:State ): x_4 v = x_4 w @-}
{-@ qualif Deref_x_l0(v:Int, w:State): v = x_l0 w @-}
{-@ qualif Eq_x_l0(v:State, w:State ): x_l0 v = x_l0 w @-}
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
                   pidR2PtrW0 :: Map_t Int Int, x_4 :: Map_t Int (Val (Pid_pre Int)),
                   x_l0 :: Int, r2 :: Int, pidR2PcK :: Map_t Int Int, pidR2K :: Int,
                   x_1 :: Int}


data Pid_pre p1 = PIDR0
                | PIDR2 p1
type Pid = Pid_pre Int
isPidR0 PIDR0 = (True)
isPidR0 _ = (False)
isPidR2 (PIDR2 ir2) = (True)
isPidR2 _ = (False)


{-@ measure isPidR0 @-}
{-@ measure isPidR2 @-}



