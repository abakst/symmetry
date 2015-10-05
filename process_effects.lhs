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

(>>=)      :: \forall (i : role) (a b : u),
              Process i x:a [G | p]
           -> (x:a -> Process i y:b [H | q])
           -> Process i y:b (join(G,H) | seq(p, q))

dom(-) = \empty
dom(l -> P@{x | p} | G) = {l} \cup dom(G)

join(-,H)                = H
join(l->P@{x | p} | G,H) 
  | l -> P@{y | q} \in H = l -> P@{z | elems z = elems x \cup elems y}; join(G, H)
  | l \not\in dom(H)     = l -> P@{x | p}; join(G, H) 

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
