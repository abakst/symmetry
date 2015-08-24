module API where

{-@ measure stmt :: Process a -> AStmt @-}
{-@ measure pid_of :: Pid -> Pid @-}

{-@ measure sskip :: Int @-}
{-@ measure sseq :: Int -> Int -> Int @-}
{-@ measure ssend :: Pid -> a -> Int @-}

data Pid
data Process a 
  
data AStmt = ASkip
           | ASend Pid
           | ARecv Pid
           | ASeq AStmt AStmt
 
{-@ measure sequence :: AStmt -> AStmt -> AStmt @-}       
sequence s1@(ASend p) s2@(ARecv q) = s1 `ASeq` s2
sequence s1 s2 = s1 `ASeq` s2
  
{-
{ stmt(v) = recv(tag x) } `seq` {stmt(v) = send(shift(I(0)), tag(foo))}
recv `seq` \p -> send p foo
-}
 
{-@
sseq :: 
        x:Process a
     -> y:Process b
     -> {v:Process b | stmt v = sequence(stmt x, stmt y) }
@-}
sseq :: Process a
     -> Process b
     -> Process b
sseq = undefined
     
{-@ skip :: {v:Process a | stmt v = ASkip } @-} 
skip :: Process a
skip = undefined
      
{-@ send :: p:Pid -> y:b -> {v:Process a | stmt v = ASend (pid_of p) } @-}
send :: Pid -> b -> Process a
send = undefined
      
-- forever :: ??? 
-- for :: ???
     
{-@ measure i :: Int -> Pid @-}
{-@ measure db :: a -> Int @-} 
{-@ recv :: {v:Process a | stmt(v) = ARecv (i 0) } @-} 
recv :: Process a
recv = undefined
     
{- foo :: p:Pid -> {v:Process a | (stmt v) = sequence (ASend (pid_of p)) (ASkip)} @-}
{- foo :: () -> {v:Process a | (stmt v) = ASeq (ASend (pid_of p)) (ASkip)} @-}
foo :: () -> Process a
foo () = recv `sseq` recv

{-@ foo2 :: {v:Process a | true } @-}
foo2 :: Process a
foo2 = foo ()

{-
  recv();recv();send(2,t)
  recv `seq` (\p -> recv `seq` \_ -> send p)
-}
