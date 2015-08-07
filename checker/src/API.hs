module API where

{-@ measure stmt :: Process a -> Int @-}
{-@ measure pid_of :: Pid -> Pid @-}

{-@ measure sskip :: Int @-}
{-@ measure sseq :: Int -> Int -> Int @-}
{-@ measure ssend :: Pid -> a -> Int @-}

data Pid
data Process a 
 
{-@
sseq :: x:Process a
    -> y:Process a
    -> {z:Process a | stmt z = sseq (stmt x) (stmt y)}
@-}
sseq :: Process a
    -> Process a
    -> Process a
sseq = undefined
     
{-@ skip :: {v:Process a | stmt v = sskip} @-} 
skip :: Process a
skip = undefined
      
{-@ send :: p:Pid -> y:b -> {v:Process a | stmt v = ssend (pid_of p) y} @-}
send :: Pid -> b -> Process a
send = undefined
     
{- foo :: p:Pid -> {v:Process a | ((stmt v) = (sseq (ssend (pid_of p) 3) sskip)) } @-}
foo :: Pid -> Process a
foo p = send p (3 :: Int) `sseq` skip 
