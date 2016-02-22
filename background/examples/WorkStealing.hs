module WorkStealing where

import Control.Monad
import Control.Distributed.Process
import Control.Distributed.Process.Closure
import PrimeFactors

{- 
slave :: ∀mq. (<m>, <q>)
      -> P me < me ▹ μX. send(q, me); { recv(Int); send(m, Int); X
                                      , recv(tt)
                                      };
              > ()
-}
slave :: (ProcessId, ProcessId) -> Process ()
slave (master, workQueue) = do
    us <- getSelfPid
    go us
  where
    go us = do
      -- Ask the queue for work
      send workQueue us

      -- If there is work, do it, otherwise terminate
      receiveWait
        [ match $ \n  -> send master (numPrimeFactors n) >> go us
        , match $ \() -> return ()
        ]

remotable ['slave]

-- | Wait for n integers and sum them all up
{- 
sumIntegers :: Int 
            -> P me < me ▹ foreach (i ∈ [1..n]):
                             recv(Integer)
                    > Integer
-}
sumIntegers :: Int -> Process Integer
sumIntegers = go 0
  where
    go :: Integer -> Int -> Process Integer
    go !acc 0 = return acc
    go !acc n = do
      m <- expect
      go (acc + m) (n - 1)
         
{-
G = foreach (i ∈ [1..n]);
      ∃p ∈ p[]. p --> q <ProcessId p>; q --> p <Integer>; p --> me<Integer>;
    μX. ∃p ∈ p[]. p --> q <ProcessId p>; q --> p <tt>; X

G ↑ (p ∈ p[]) = foreach(i ∈ [1..n]):
                  send(q, ProcessId p); recv(Integer); send(me, Integer);
                send(q, ProcessId p); recv(tt);

G ↑ q         = foreach(i ∈ [1..n):
                  ∃p ∈ p[]. recv(ProcessId p); send(p, Integer);
                μX. ∃p ∈ p[]. recv(ProcessId p); send(p, tt);
                        
G ↑ me        = foreach(i ∈ [1..n):
                  recv(Integer);
-}

{-
master :: Integer -> [NodeId]
       -> P me < q             ▹ foreach (i ∈ [1..n]):
                                   ∀p. recv(p); send(p, Integer);
                                 μX. ∀p. recv(p); send(p, tt); X
                 p[len slaves] ▹ μX. send(q, me); { recv(Int); send(me, Int); X
                                                  , recv(tt)
                                                  };
                 me            ▹ foreach (i ∈ [1..n]):
                                   recv(Integer)
               > Integer
-}
{-
  SCRATCH:::::
master :: Integer -> [NodeId]
       -> P me < q             ▹ foreach (i ∈ [1..n]):
                                   ∀p. recv(p); send(p, Integer);
                                 μX. ∀p. recv(p); send(p, tt); X
                 p[len slaves] ▹ foreach (i ∈ [1..n/len slaves]):
                                   send(q, me); recv(Int); send(me, Int); X
                                 μX. send(q, me); { recv(Int); send(me, Int); X
                                                  , recv(tt)
                                                  };
                 me            ▹ foreach (i ∈ [1..n]):
                                   recv(Integer)
               > Integer
-}
{-
< q             ▹ foreach (i ∈ [1..n]):
                    recv(p'); send(p', Integer);
                  μX. ∀p. recv(p); send(p, tt); X
  p[len slaves] ▹ μX. send(q, me); { recv(Int); send(me, Int); X
                                   , recv(tt)
                                   };
  p'            ▹ foreach(i ∈ [1..n]):
                   recv(Int); send(me, Int);
                  μX. send(q, me); { recv(Int); send(me, Int); X
                                   , recv(tt)
                                   };
  me            ▹ foreach (i ∈ [1..n]):
                    recv(Integer)
>
-}
master :: Integer -> [NodeId] -> Process Integer
master n slaves = do
  us <- getSelfPid

  workQueue <- spawnLocal $ do
    -- Reply with the next bit of work to be done
    forM_ [1 .. n] $ \m -> do
      them <- expect
      send them m

    -- Once all the work is done, tell the slaves to terminate

    -- This deadlocks, but all we want is the termination
    -- of the master node
    forever $ do
      pid <- expect
      send pid ()

  -- Start slave processes
  forM_ slaves $ \nid -> spawn nid ($(mkClosure 'slave) (us, workQueue))

  -- Wait for the result
  sumIntegers (fromIntegral n)
