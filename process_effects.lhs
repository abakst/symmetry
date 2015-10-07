\begin{code}
module ProcessEffects where
import Control.Distributed.Process
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
            (\p -> send p ()) -- p:Pid -> Process i () [ - | send({v:Pid | v = p}, ())]
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
ex3 :: Process ()
ex3 = do
  me <- getSelfPid
  p  <- spawn (send me ())
  expect :: Process ()
  return p
\end{code}

spawnLoop :: \forall i j : Role,
        Process j () [ - | P ]
     -> (x:Int -> Process i {r:[Pid] | length r = x} [j -> P@{v | elems v = elems r} | 0]) 
     -> x:Int 
     -> Process i {r:[Pid] | length r = x} [j -> P@{v | elems v = elems r} | 0])
\begin{code}
spawnLoop p f 0
  = return []
spawnLoop p f n
  = do pid  <- spawnLocal p 
       pids <- f (pred n)
       return (pid : preds)
\end{code}
       
fix :: ((x:a -> Process i a [G | P]) -> (x:a -> Process i a [G | P]))
    -> (x:a -> Process i a [G | P])

\begin{code}
spawnN :: Int -> Process () -> Process [ProcessId]
spawnN n p = fix (spawnLoop p) n
\end{code}
       
messageLoop :: \forall i : Role,
               (ps:[Pid] -> Process i () [ - | foreach (p : ps): send(p, Ping)])
            -> ps:[Pid] 
            -> Process i () [ - | foreach (p : ps): send(p, Ping)])
\begin{code}
messageLoop f []
  = return ()
messageLoop f (p:ps)
  = (>>=) (send p Ping)
          (\_ -> f ps)
\end{code}
        
       
foo :: \forall i j : Role,
       n:Int
    -> Process i () [j -> recv(_:Ping)@{v | size v = n} | foreach (p : j): send(p, Ping)]
\begin{code}
foo n = (>>=)
        -- Process {ps:[Pid] | length r = n} [j -> recv(_:Ping)@{v|elems v = ps} | 0] 
        (spawnN n
          (expect >> return ()))
        --Process () [ - | foreach (p \in ps): send(p, Ping) ]
        (fix messageLoop ps)
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
  
G |- i :: role
G |- t
G |- receive i t :: t_0 & r. [ - | recv(r:t)
 
G |- i :: role 
G |- x :: tx 
G |- tx <: Pid
G |- e :: te
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
G |- H1 cup H2 <= H
G;x:t1, H |- P1; P2 <= P
----------------------------------
G |- x <- m; n :: t2 & [ H | P ]_i
  
Simulation:

G |- xs : t
H(l) = {v | elems v = xs}
-----------------------------------------------
G, H |- foreach(x : xs): p <= foreach(x : l): p

G |- xs : t
H(l) = {v | elems v = (x : xs)}
-----------------------------------------------
G, H |- p; foreach(x : xs'): p <= foreach(x : xs): p

Join:

G;x:{v | a};y:{v | a'} |- {v | v = x \cup y} <: {v | a''}
G |- H1 cup H2 <= H
----------------------------------------------------------------
G |- l -> P@{v | a} cup l -> P{v | a'}*H1 <= l -> P@{v | a''}*H2
