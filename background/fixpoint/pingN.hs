{-@ LIQUID "--no-termination" @-}
module Foo() where 

import Data.Map
import Language.Haskell.Liquid.Prelude (liquidAssume, liquidAssert)

{-@ sched :: {v:[{v:Int | true}] | true} @-}
sched :: [Int]         
sched = undefined


{-@ nonDetPos :: {v:Int | v > 0} @-}              
nonDetPos :: Int
nonDetPos = undefined

data PC = L0 | L1 | L2 | L3 deriving (Eq)           

type AState = (Int, Int, Int, PC)        
type BState = (Int, Int, Int, PC)

-- State is:         N      PTRR   PTRW   A_I    I      PCA   PCB
runState :: [Int] -> Int -> Int -> Int -> Int -> Int -> PC -> PC -> ()
runState [] _ _ _ _ _ _ _
  = liquidAssume (0 == 1) ()
-- A: exit loop?
runState (0:ss) n a_i b_i ptrr ptrw L0 pcb
  | a_i < n   = runState ss n a_i b_i ptrr ptrw L1 pcb
  | otherwise = runState ss n a_i b_i ptrr ptrw L3 pcb
--A: send to B
runState (0:ss) n a_i b_i ptrr ptrw L1 pcb
  = runState ss n a_i b_i ptrr (ptrw + 1) L2 pcb
--A: inc i; goto loop
runState (0:ss) n a_i b_i ptrr ptrw L2 pcb 
  = runState ss n (a_i + 1) b_i ptrr ptrw L0 pcb 
--A: done
runState (0:ss) n a_i b_i ptrr ptrw L3 pcb
  = runState ss n a_i b_i ptrr ptrw L3 pcb

--B: exit loop?    
runState (1:ss) n a_i b_i ptrr ptrw pca L0 
  | b_i <  n  = runState ss n a_i b_i ptrr ptrw pca L1
  | otherwise = runState ss n a_i b_i ptrr ptrw pca L3
--B: recv()
runState (1:ss) n a_i b_i ptrr ptrw pca L1
  | ptrr < ptrw = runState ss n a_i b_i (ptrr + 1) ptrw pca L2
  | otherwise   = runState ss n a_i b_i ptrr ptrw pca L1
--B: inc i;goto loop
runState (1:ss) n a_i b_i ptrr ptrw       pca L2
  = runState ss n a_i (b_i + 1) ptrr ptrw pca L0
--B: done
runState (1:ss) n a_i b_i ptrr ptrw pca L3
  = runState ss n a_i b_i ptrr ptrw pca L3

-- assert deadlock free
runState _ n a_i b_i ptrr ptrw pca pcb 
  = liquidAssert (not (pca == L3 && pcb == L1 && ptrr >= ptrw)) ()

{-@ doCheck :: {v:() | true} @-}
doCheck :: ()
doCheck = runState sched nonDetPos 0 0 0 0 L0 L0 

{-@ qualif I1(v:PC, x:Int, b_i:Int): ((v = L0 || v = L1) => (b_i = x)) @-}
{-@ qualif I2(v:PC, x:Int, b_i:Int): ((v = L2) => (b_i = x - 1)) @-}
{-@ qualif I3(v:PC, x:Int, n:Int): ((v = L1) => (x < n)) @-}
{-@ qualif I4(v:PC, x:Int, n:Int): ((v = L3) => (x >= n)) @-}
