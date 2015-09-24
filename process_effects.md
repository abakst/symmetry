# Effect Tracking for Processes

## Process Types

First, let us give actions `m` types of the following form:

~~~~
m :: P i x:a E
~~~~

Where:

- `x:a` denotes that the returned value of the process is bound to `x` and has type `a`,
- `i` is a channel (type `ch`) (for the current process),
- `E` is the effect of the current process, which is a program in a process calculus whose
terms are denoted by the metavariable `p`. In this language, communication between processes
is over a set of named *chnnels* (`c`):

~~~~
p ::= 0
   | RECV(x:a).p -- receive a message of type a, bind it to x, then continue as p.
   | SEND(c,a).p -- send a message of type a on ch c, then continue as p.
   | μX.p
   | X
   | p + p
   | p & p

E = 0 | i ~> p * E
~~~~

## API

Let us then write some specifications using these ideas. Let's assume
a function `chan :: Pid -> ch` that maps Haskell `Pid` values to
their associated `ch`. We will need a precise abstraction to
handle reasoning about `Pids`, so I am using refinement types because
I like them.

Here, `getSelfPid` returns a `Pid` such that the associated ch is
equal to the ch of the current process.

The "up arrow" type `x::↑a` should be ignored for now.

~~~~
getSelfPid :: Π i:ch, P i x:{v:Pid | chan v = i} [i~>0]
~~~~

~~~~
recv :: Π i:ch, P i x:↑a [i ~> RECV({x:a | TRUE})]

send :: Π i:ch,
        Π p:Pid,
     -> a
     -> P i x:unit (i ~> SEND(chan p, a))

spawn :: Π i j:ch,
         P j x:unit E
      -> P i {v:Pid | chan v = j} (E * i ~> 0)
~~~~

Both `recv` and `send` introduce a singleton effect: either `RECV`-ing
a value and binding it to `x`, or `SEND`-ing a value.

~~~~
(>>=) :: Π {i:ch}.
         P i (x:a) E1
      -> (y:a -> P i (z:a) E2)
      -> P i (z:a) (join(i, E1, E2[y := x]))

join(i, i ~> p1 * E1, i ~> p2 * E2) = i ~> p1;p2 * join(i, E1, e2)
join(i, E1, E2)                     = E1 * e2
~~~~

`>>=` conjoins the effects of each parallel process while sequencing
the effects of the 'current' process.

## Examples

~~~~{.haskell}
x :: ↑Pid, i :: ch |- send {i} x 3 :: P i r:() i~>SEND(chan x, Int)

ex1 :: Π {i:ch}, P i r:() [i ~> RECV(x:Pid).SEND(chan x, Int)]
ex1 = do x <- recv {i}
         send {i} x 3
~~~~

~~~~

x::↑Pid,
i::ch
---------- (1)
\me::{v:Pid | chan v = i} -> send x {i} me :: P i r:() i~>SEND(chan x, {v:Pid | chan v = i})


i :: ch
(1)
------------ (2)
\x -> getSelfPid {i} >>= \me -> send x {i} me in :: P i r:() i~>SEND(chan x, {v:Pid | chan v = i})

ex2 :: Π {i:ch}. P i r:() i~>RECV(x:PID).SEND(chan x, {v:Pid | chan v = i})

ex2 = do x <- recv [i]
         me <- getSelfPid [i]
         send [i] x me
-- ex2 {i} = recv {i} >>= (\x -> getSelfPid {i} >>= (\me -> send {i} x me))
~~~~

~~~~{.haskell}
i :: ch,
j :: ch,
p :: {v:Pid | chan v = j}
------------------------- (1)
send {i} p () :: P i (r:()) i~>SEND(j, ())

i :: ch,
j :: ch
------------- (2)
recv {j} :: P j (r:↑()) j~>RECV(r:())

i :: ch,
j :: ch,
(2)
-------------- (3)
spawn {i j} (recv {j}) :: P i (r:{v:Pid | chan v = j}) (i~>0 * j~>RECV(r:()))

i :: ch,
j :: ch,
(1, 3)
-------------
(>>= {i}) (spawn {i j} (recv {j})) (\p -> send {i} p ()) :: P i (r:()) {i~>SEND(j, ()) * j~>RECV(r:())}


ex3 :: Π {i j:ch}.P i (r:()) {i~>SEND(j, ()) * j~>RECV(r:())}
ex3 = do p <- spawn {i j} (recv {j})
         send p ()
~~~~

~~~~{.haskell}
i :: ch
foo :: Pid
--------------- (1)
getSelfPid {i} :: P i {v:Pid | chan v = i} i~>0

i :: ch,
foo :: Pid
me :: {v:Pid | chan v = i}
-------------------------- (2)
send foo me :: P i (r:()) i~>SEND(chan foo, {v:Pid | chan v = i})

i :: ch,
foo :: Pid,
(1, 2)
-------------
(>>= {i}) (getSelfPid {i}) (send {i} foo me) :: P i (r:()) (i~>SEND(chan foo, {v:Pid | chan v = i}))

p foo :: Π {i:ch}. Π foo:Pid. P i (R:()) i~>SEND(chan foo, {v:Pid | chan v = i})
p foo = do me <- getSelfPid {i}
           send foo me

i, j :: ch
me :: {v:Pid | chan v = i }
--------------------------- (3)
spawn {i j} (p {j} me) :: P i (r:{v:Pid | chan v = j}) (i~>0 * j~>SEND(i, {v:Pid | chan v = j}))

i, j :: ch
me :: {v:Pid | chan v = i }
(3)
---------------------------- (4)
(>>= {i}) (spawn {i j} (p {j} me)) (recv {i}) :: P i (r:a) (i->RECV(r:Pid) * j~>SEND(i, {v:Pid | chan v = j}))

ex4 :: Π {i j:ch}. P i r:Pid (i~>RECV(r:Pid) * j~>SEND(i, {v:Pid | chan v = j}))
ex4 = do me <- getSelfPid {i}
         p1 <- spawn {j} (p {j} me) 
         recv {i} 
~~~~

### Recursion?
~~~~{.haskell}
forM :: Π i:ch.
        [a]
     -> (x:a -> P i (r:b) E)
     -> P i (y:[b]) E*???
~~~~

~~~~{.haskell}

master :: Π {chans : [Ch]}.
          Π peers:{v:[NodeId] | len v = len chans}.
       -> P ???
master {chans} peers = do
  ps <- forM peers $ \nid -> do
          say $ printf "spawning on %s" (show nid)
          -- P chans
          spawn nid $(mkStaticClosure 'pingServer)
~~~~
