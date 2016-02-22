module MasterSlave where

import Control.Monad
import Control.Distributed.Process
import Control.Distributed.Process.Closure
import PrimeFactors

{-
slave :: (ProcessId<p>, Integer)
      -> Process me < me ▹ send(p, Integer) > ()
-}
slave :: (ProcessId, Integer) -> Process ()
slave (pid, n) = send pid (numPrimeFactors n)

remotable ['slave]

-- | Wait for n integers and sum them all up
{-
sumIntegers :: n:Int
            -> Process me < me ▹ foreach (i ∈ [1..n]): recv(Integer); > Integer
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
sumIntegers' :: n:Int
            -> Process me < me ▹ foreach (i ∈ [1..n]): recv(Integer); > Integer
-}
sumIntegers' :: Int -> Process Integer
sumIntegers' = foldM go 0 [1..n] 
    where
      {- go :: Integer -> Int -> Process me < me ▹ recv(Integer) > Integer -}
      go :: Integer -> Int -> Process Integer
      go !acc _ = do
        m <- expect
        return (acc + m)
    

data SpawnStrategy = SpawnSyncWithReconnect
                   | SpawnSyncNoReconnect
                   | SpawnAsync
  deriving (Show, Read)
           
{- 
G(n) = foreach (p ∈ p[n]): 
         p --> me <Integer>;

G(n) ↑ (p ∈ p[n]) = send(me, Integer)
G(n) ↑ me         = foreach (p ∈ p[n]): recv(Integer)
-}
           
{-
master :: n:Integer
       -> SpawnStrategy
       -> NodeId
       -> Process me < me    ▹ foreach (i ∈ [1..n]): 
                                 recv(Integer); 
                       p ∈ P ▹ send(me, Integer);
                     > Integer
-}
master :: Integer -> SpawnStrategy -> [NodeId] -> Process Integer
master n spawnStrategy slaves = do
  {- us :: ProcessId <me> -}
  us <- getSelfPid

  -- Distribute 1 .. n amongst the slave processes
  spawnLocal $ case spawnStrategy of
    SpawnSyncWithReconnect ->
      forM_ (zip [1 .. n] (cycle slaves)) $ \(m, there) -> do
        them <- spawn there ($(mkClosure 'slave) (us, m))
        reconnect them
    SpawnSyncNoReconnect ->
      forM_ (zip [1 .. n] (cycle slaves)) $ \(m, there) -> do
        _them <- spawn there ($(mkClosure 'slave) (us, m))
        return ()
    SpawnAsync ->
      forM_ (zip [1 .. n] (cycle slaves)) $ \(m, there) -> do
        spawnAsync there ($(mkClosure 'slave) (us, m))
        _ <- expectTimeout 0 :: Process (Maybe DidSpawn)
        return ()

  -- Wait for the result
  sumIntegers (fromIntegral n)
