{-@ LIQUID "--no-termination" @-}
module Foo() where 

import Language.Haskell.Liquid.Prelude (liquidAssume, liquidAssert)

{-@ sched :: n:Int 
          -> m1:Map Int Int 
          -> m2:Map Int Int
          -> m3:Map Int PC 
          ->[{v:Sched<{i:Int | 0 <= i && i < n && Map_select m1 i = 0 && Map_select m2 i = 0 && (Map_select m3 i = L0 || Map_select m3 i = L1)}> | true}] @-}
sched :: Int -> Map Int Int -> Map Int Int -> Map Int PC -> [Sched]         
sched = undefined

{-@ data Sched <p :: Int -> Prop> = PA | PB { fooo :: Int<p> } @-}
data Sched = PA | PB Int

{-@ nonDetPos :: {v:Int | v > 0} @-}              
nonDetPos :: Int
nonDetPos = undefined

data Map a b = M (a -> b)
{-@ embed Map as Map_t @-}                 
{-@ measure Map_select :: Map a b -> a -> b @-}
{-@ measure Map_store :: Map a b -> a -> b -> Map a b @-}

{-@ emp :: {v:Map Int {v:Int | v = 0} | true} @-} 
emp :: Map Int Int
emp = undefined

{-@ empZero :: {v:Map Int Int | true} @-} 
empZero :: Map Int Int
empZero = undefined

{-@ empPC :: {v:Map Int PC | true} @-} 
empPC :: Map Int PC
empPC = undefined
       
{-@ get :: m:Map a b -> k:a -> {v:b | v = Map_select m k } @-}
get :: Map a b -> a -> b
get m k = undefined

{-@ put :: m:Map a b -> k:a -> val:b -> {v:Map a b | v = Map_store m k val } @-}
put :: Map a b -> a -> b -> Map a b 
put m k v = undefined

{-@ data PC = L0 | L1 | L2 @-}
data PC = L0 | L1 | L2 deriving (Eq)           

runState :: Int -> Int -> Map Int Int -> Map Int Int -> PC -> Map Int PC -> [Sched] -> ()
-- Assert deadlock-freedom (deadlock if A is done and B(i) is blocked)
runState  n a_i m_wr m_rd pca m_pcb [PB i]
  = liquidAssert (not (pca == L1 && get m_pcb i == L0 && get m_rd i >= get m_wr i)) ()
-- A: exit loop?
runState n a_i m_wr m_rd L0 m_pcb (PA:ss)
  = if a_i < n then
      runState n a_i m_wr m_rd L2 m_pcb ss
    else
      runState n a_i m_wr m_rd L1 m_pcb ss
-- A: loop body
runState n a_i m_wr m_rd L2 m_pcb (PA:ss) 
  = runState n (a_i + 1) (put m_wr a_i (get m_wr a_i + 1)) m_rd L0 m_pcb ss
-- A: <done>
runState n a_i m_wr m_rd L1 m_pcb (PA:ss) 
  = runState n a_i m_wr m_rd L1 m_pcb ss

runState n a_i m_wr m_rd pca m_pcb ((PB i):ss)    
   --B: recv()
  | (pca == L1 && get m_pcb i == L0 && get m_rd i >= get m_wr i) = liquidAssert False ()
  | get m_pcb i == L0 &&
    get m_rd i < get m_wr i
      = runState n a_i m_wr (put m_rd i (get m_rd i + 1)) pca (put m_pcb i L1) ss
   --B: <done>
  | get m_pcb i == L1 = runState n a_i m_wr m_rd pca m_pcb ss
  | otherwise         = runState n a_i m_wr m_rd pca m_pcb ss

-- runState _ n a_i m_wr m_rd pca m_pcb 
--   = liquidAssume False ()

{- doCheck :: {v:() | true} @-}
doCheck :: ()
doCheck = runState nonDetPos 0 emp emp L0 empPC (sched nonDetPos emp emp empPC)

{-@ qualif I0a(v:Int, m:Map_t Int Int, x:Int): ((0 <= v && v < x) => Map_select m v > 0) @-}        
{-@ qualif I0c(v:Int, m:Map_t Int PC, m2:Map_t Int Int): (Map_select m v = L0 => Map_select m2 v = 0) @-}
{-@ qualif I0d(v:Int, m:Map_t Int PC, m2:Map_t Int Int): (Map_select m v = L1 => Map_select m2 v = 1) @-}
{-@ qualif I3(v:PC, x:Int, n:Int): ((v = L0) => (x <= n)) @-}
{-@ qualif I4(v:PC, x:Int, n:Int): ((v = L1) => (x >= n)) @-}
{-@ qualif I5(v:PC, x:Int, n:Int): ((v = L2) => (x < n)) @-}
