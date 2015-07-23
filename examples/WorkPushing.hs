module WorkPushing where

import Control.Monad
import Control.Distributed.Process
import Control.Distributed.Process.Closure
import PrimeFactors

{- Interesting: The "slave" processes eventually deadlock, but
                we don't care because the master process does not... 
 -}

slave :: ProcessId -> Process ()
{- ∀p. <p> -> P me < me ▹ μX. recv(Int); send(p, Int); X > -}
slave them = forever $ do
  n <- expect
  send them (numPrimeFactors n)

remotable ['slave]

-- | Wait for n integers and sum them all up
sumIntegers :: Int -> Process Integer
sumIntegers = go 0
  where
    go :: Integer -> Int -> Process Integer
    go !acc 0 = return acc
    go !acc n = do
      m <- expect
      go (acc + m) (n - 1)
         
{-
G = foreach (i ∈ [1..n]):
      ∃p ∈ p[]. me --> p <Integer>;
                p --> me <Integer>

G ↑ (p ∈ p[]) = foreach (i ∈ [1..n]):
                  recv(Integer);
                  send(me, Integer);

G ↑ me        = foreach (i ∈ [1..n]):
                  ∃p ∈ p[]. send(p, Integer);
                            recv(Integer);
-}
         
{- 
master :: n:Integer
       -> [NodeId]
       -> Process me < p[] ▹ μX. recv(Int); send(me, Integer); X
                       me  ▹ foreach (i ∈ [1..n]):
                               choose(p ∈ p[]). send(p, Integer);
                             foreach (i ∈ [1..n]):
                               recv(Integer);
                     > Integer
-}


{-
SCRATCH::
< p[] ▹ μX. (recv(Int); send(me, Integer); X
              & recv(tt); end)
  me  ▹ foreach (i ∈ [1..n]):
          choose(p ∈ p[]). send(p, Integer);
        foreach (i ∈ [1..n]):
          recv(Integer);
   r  ▹ foreach (p ∈ p[]):
          send(p, tt);
-}                              

{-

B -> A choose(1);
B -> A <Left>;
A -> B <Int>;
C -> A choose(2);
C -> A <Left>;
A -> C <Int>

  A [ { recv(Left); send(B, Int);
        recv(Right); send(C, String);
      };
      { recv(Left); send(B, String);
        recv(Right); send(C, Int);
      };
    ]
  B [ send(A, Left); recv(Int); ]
  C [ send(A, Right); recv(Int); ]
-}
master :: Integer -> [NodeId] -> Process Integer
master n slaves = do

  us <- getSelfPid

  -- Start slave processes
  slaveProcesses <- forM slaves $ \nid -> spawn nid ($(mkClosure 'slave) us)

  -- Distribute 1 .. n amongst the slave processes
  spawnLocal $ forM_ (zip [1 .. n] (cycle slaveProcesses)) $
    \(m, them) -> send them m

  -- Wait for the result
  sumIntegers (fromIntegral n)
