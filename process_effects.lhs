\begin{code}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing  #-}
import Control.Monad
import Control.Distributed.Process
import Data.Binary
import Data.Typeable
import GHC.Generics (Generic)
\end{code}
        
P ::= 0
    | recv(x:t)  //recv a value of type t, bind to x
    | send(x,u)  //send a value of type u to x
    | P; P       
    | case x of {... Pattern_i -> P_i ...}
    | foreach (e : es): P

Let a "role" be a name for a set of Pids.
An environment of running processes is defined

G ::= -  
    | l -> P@{x:PidSet | p }; G
  
The environment 

l -> P@{x:PidSet | p}
  
says that the role l:

(1) denotes processes all running the program P
(2) is inhabited by a set of Pids, x, such that p holds 
    (ie {x:PidSet | p} is a refinement type)

Thus, the type 

m :: Process i r:a [ G | P ]

denotes a process that:

  (1) returns a value of type a (bound to r, which may appear in P)
  (2) behaves as P in role i
  (3) spawns the environment G
  
----------
API  
----------

return     :: \forall i:role a:t, a 
           -> Process i a [- | 0 ]

expect     :: \forall i:Role a:t, 
              Process i x:a [ - | recv(x:a) ]

send       :: \forall i:Role a:t,
              p:Pid 
           -> a  
           -> Process x:() [ - | send(p, a) ]

getSelfPid :: \forall i:Role, 
              Process i x:{v:Pid | role v = i} [ - | 0 ]

spawn   :: \forall i j : Role,
           Process j () [0 | p] 
        -> Process i x:Pid [let j = new p; j -> {v | elems v = {x}}| 0]

(>>=)      :: \forall (i : role) (G1 G2 H : env) (p q r : proc),
              { join(G1, G2) < H 
              , join(G1, G2); x:a => seq(p, q) < r
              }
           => Process i x:a [G1 | p]
           -> (x:a -> Process i y:b [G2 | q])
           -> Process i y:b (H | r)

ex1 :: \forall i:Role, 
       Process i () [ - | recv(p:Pid);send({v:Pid | v = p}, ()) ]
\begin{code}
ex1 :: Process ()
ex1 = (>>=) expect -- Process i p:Pid [ - | recv(p:Pid) ]
            (`send` ()) -- p:Pid -> Process i () [ - | send({v:Pid | v = p}, ())]
\end{code}

ex2 :: \forall i:Role, 
       Process i () [ - | recv(x:Pid); 0; send({v:Pid | v = x}, {v:Pid | role v = i})]
\begin{code}
ex2 :: Process ()
ex2 = do
  x  <- expect
  me <- getSelfPid
  send x me
\end{code}

ex3 :: \forall i j:Role, 
       Process i {r:Pid | role r = j} [ j -> send({v:Pid | role v = i}, ())@{v | len v = 1 } | recv(x:()) ]
\begin{code}
ex3 :: Process Pid
ex3 = do
  me <- getSelfPid
  p  <- spawnLocal (send me ())
  expect :: Process ()
  return p
\end{code}
        
R b g@(\X x -> foo) (x:xs) = g (R b g xs) x

R (return ()) (\X _ -> spawn bloo >> X) [1,2,3] == (\X _ -> spawn bloo >> X) (R (return ()) (\X _ -> spawn bloo >> X) [2,3]) 1
                                                == spawn bloo >> (R (return ()) (\X _ -> spawn bloo >> X) [2,3]
                                                == spawn bloo >> (\X _ -> spawn bloo >> X) (R (return ()) (\X _ -> spawn bloo >> X) [3]) 2
                                                == spawn bloo >> spawn bloo >> (R (return ())

mKont :: Process i [Pid] & r. [ j |> (P,{v|elems v = r}) | 0 ]
spawnN p = R (return ()) (\mKont _ -> do pid  <- spawnLocal p
                                         pids <- mKont
                                         return (pid : pids)) xs

G |- a :: Process a & r. [ H0 | P0 ]
G |- f :: x:a -> y:b -> Process a & r. [ H1 | P1 ]
G |- xs :: [b]
G, r:a |- H1[(x:r) := r] ⊔ H1 <= H
--------------                                         
foldM f a xs :: Process [a] & r. [ H | P0; foreach (x:xs): P ]

H[r := ps]
foldM 
  (\pids x -> spawnLocal foo >>= \p -> (return p:pids)) :: ps:[Pid] -> x:Int -> Process [Pid] & r. [ 
  []
  xs

\begin{code}
spawnN :: Process () -> Int -> Process [Pid]
spawnN p n = foldl (\m _ -> do pid <- spawnLocal p
                               pids <- m
                               return (pid : pids))
                   (return [])
                   [1..n]
\end{code}
      
Desired: 
messageLoop :: \forall i : Role,
               ps:[Pid] 
            -> Process i () [ - | foreach (p : ps): send(p, Ping)])
\begin{code}
messageLoop :: [Pid]
            -> Process ()
messageLoop []
  = return () -- Process i () [ - | 0 ]
messageLoop (p:ps)
  = do send p Ping -- Process i () [ - | send(Pid(x), Ping) ]
       messageLoop ps
\end{code}
        
       
foo :: \forall i j : Role,
       n:Int
    -> Process i () [j -> recv(_:Ping)@{v | size v = n} | foreach (p : j): send(p, Ping)]
\begin{code}
expectPing :: Process Ping
expectPing = expect 

foo :: Int -> Process ()
foo n = (>>=)
        -- Process {ps:[Pid] | length r = n} [j -> recv(_:Ping)@{v|elems v = ps} | 0] 
        (spawnN (expectPing >>= \_ ->  return ()) n)
        (mapM_ (`send` Ping))
\end{code}

Core Calculus

Types & Effects
t = Pid | Int | Bool | t -> t | t & [ H | p ]
p = send(t, t) | recv(x:t) | foreach (e : e): p | p; p 
  | case x of { Pattern -> f }
H = - | l -> p@t * H  

Expressions

e = c | x | \x -> e | e e | do m
m = return i e | receive i t | send i x e | spawn i j e | self i | x <- m; m
  | R b f e -- ugh? (primitive recursion)
  
Type Checking

G = - | x:t; G

Pure:

G(x) = t & [ H | p ]_i
----------------------
G |- x :: t & [ H | p ]_i
  
G; x:t1 |- e :: t2
------------------------
G |- \x -> e :: t1 -> t2
  
G |- e1 :: t2 -> t
G |- e2 :: t2
------------------
G |- e1 e2 :: t

Impure:
        
G |- i :: role
-----------------------------------
G |- self :: Pid(i) t & [ - | 0 ]_i

G |- i :: role 
G |- e :: t
----------------------------------
G |- return i e :: t & [ - | 0 ]_i
  
G |- t
G |- i :: role
------------------------------------------------
G |- receive i t :: t_0 & r. [ - | recv(r:t) ]_i
 
G |- i :: role 
G |- x :: tx 
G |- e :: te
base tx == Pid
---------------------------------------------
G |- send i x e :: t & [ - | send(tx, te) ]_i
  
G |- i :: role 
G |- j :: role 
G |- i != j
G |- e :: unit & [ - | p ]_j
------------------------------------------------------------------
G |- spawn i j e :: Pid(j) & r. [ j -> {v | elems v = {r}} | 0 ]_i
  
G |- m :: t1 & [ H1 | P1 ]_i
G |- x:t1 -> n :: t2 & [ H2 | P2 ]_i
G |- H1 ⊔ H2 <= H
G;x:t1, H |- P1; P2 <= P
----------------------------------
G |- x <- m; n :: t2 & [ H | P ]_i
  
G          |- i  :: role
G          |- xs :: f t
G          |- b  :: tb & r. [ - | 0 ]
G,b:tb,x:t |- m  :: tb & r. [ H | P ]
-----------------------------------
G |- R_f b m xs :: [ H | foreach (x:xs): P ]
  
Simulation:

G |- xs : t
H(l) = {v | elems v = xs}
-----------------------------------------------
G, H |- foreach(x : xs): p <= foreach(x : l): p

G |- xs : t
H(l) = {v | elems v = (x : xs)}
-----------------------------------------------
G, H |- p; foreach(x : xs'): p <= foreach(x : xs): p

Env Join:

G;x:{v | a};y:{v | a'} |- {v | v = x ∪ y} <: {v | a''}
G |- H1 ⊔ H2 <= H
----------------------------------------------------------------
G |- l |> (P, {v | a}) * H1 ⊔ l |> (P, {v | a'}) * H2 <= l |> (P, {v | a''}) * H

\begin{code}
type Pid  = ProcessId
data Ping = Ping
  deriving (Typeable, Generic)

instance Binary Ping

main :: IO ()
main = return ()
\end{code}

SCRATCH:
        
getSelfPid :: forall (i:role(0)), Process i Pid(addr i) None 

receive :: forall (t:type),
           forall (i:role(recv(t))), Process i t None
        
send  :: forall (t1 t2 : type),
         forall (i:addr), Process (role i send(t1, t2)) () None

spawn :: forall i:role(0) p:proc j:role(p),
         Process j () None
      -> Process i Pid(j) \h1 x h2 -> h2 = h1[j:=h1[j] \cup {x}]

bind :: { h1 h2 h3 : heap; x: t; y: t' |- P h1 x h2 && Q h2 y h3 => R h1 y h3 }
     => forall (p1: proc) (p2 : t -> proc) (i:role(p1;p2)),  
        Process (p1 i) t P
     -> (x:t -> (Process (p2 i) (p2 x)) t' Q))
     -> Process i t' R


\begin{code}
spawnLoop2 {- j -} 0
  = return [] -- forall i:role(0), Process i [Pid(?)] \h1 x h2 -> h1 = h2
spawnLoop2 {- j -} n
  = do p <- spawnLocal {- j -} -- Process i Pid(j) \h1 x h2 -> h2 = h1[j:=h1[j] \cup {x}]
       ps <- spawnLoop2 {- j -} (n - 1) -- Process i [Pid(j)] \h1 x h2 -> h2 = h1[j:=h1[j] \cup x]
       return (p : ps) -- Process i [Pid(j)] \h1 x h2 -> h2 = h1[j := h1[j] \cup 
\end{code}
