-- | Monomorphic "single-shot" distributed implementation of map-reduce
module MonoDistrMapReduce (distrMapReduce, __remoteTable) where

import Data.Map (Map)
import qualified Data.Map as Map (size, toList)
import Control.Monad (forM_, replicateM, replicateM_)
import Control.Distributed.Process
import Control.Distributed.Process.Closure
import MapReduce (MapReduce(..), reducePerKey, groupByKey)

--------------------------------------------------------------------------------
-- Simple distributed implementation                                          --
--------------------------------------------------------------------------------

mapperProcess :: (ProcessId, ProcessId, Closure (MapReduce String String String Int Int))
              -> Process ()
mapperProcess (master, workQueue, mrClosure) = do
    us <- getSelfPid
    mr <- unClosure mrClosure
    go us mr
  where
    {- P me < me ▹ μX. send(workQueue, me); 
                       { recv(String, String); send(master, [(String, Int)]); X;
                       , recv(tt);
                       }
            > ()
     -}
    go us mr = do
      -- Ask the queue for work
      send workQueue us

      -- Wait for a reply; if there is work, do it and repeat; otherwise, exit
      receiveWait
        [ match $ \(key, val) -> send master (mrMap mr key val) >> go us mr
        , match $ \()         -> return ()
        ]

remotable ['mapperProcess]
{- 
G = foreach (x ∈ input):
      ∃(p ∈ p[n]). p --> workQueue <ProcessId p>; 
                   workQueue --> p <(String, String)>; 
                   p --> me <[(String, String)]>;
    foreach (p ∈ p[n]):
      p --> workQueue <ProcessId p>; workQueue --> p <tt>;

G ↑ (p ∈ p[n]) = foreach (x ∈ input): 
                   send(workQueue, ProcessId p);
                   recv((String, String));
                 send(workQueue, Process p); recv(tt);

G ↑ workQueue  = foreach (x ∈ input):
                   ∃(p ∈ p[n]). recv(ProcessId p); 
                                send(p, (String, String)); 
                 foreach (p ∈ p[n]):
                   ∃(p ∈ p[n]). recv(ProcessId p); 
                                send(p, tt);

G ↑ me         = foreach (x ∈ input):
                   recv([(String, Int)]);
-}
      
{-
distrMapReduce :: Closure (MapReduce String String String Int Int)
               -> [NodeId]
               -> Map String String
               -> Process me < workQueue ▹
                                 foreach (x ∈ input): 
                                   ∀p. recv(p); send(p, (String, String));
                                 foreach (i ∈ [0..length mappers - 1]):
                                   ∀p. recv(p); send(p, tt);
                               p[n]      ▸ μX. send(workQueue, p[i]);
                                               (recv(String, String); send(master, [(String, String)]); X
                                                & recv(tt));
                               me        ▹ foreach (x ∈ input):
                                             recv([(String, Int)])
                             > (Map String Int)
-}

distrMapReduce :: Closure (MapReduce String String String Int Int)
               -> [NodeId]
               -> Map String String
               -> Process (Map String Int)
distrMapReduce mrClosure mappers input = do
  mr     <- unClosure mrClosure
  master <- getSelfPid
             
  workQueue <- spawnLocal $ do
    -- Return the next bit of work to be done
    forM_ (Map.toList input) $ \(key, val) -> do
      them <- expect
      send them (key, val)

    -- Once all teh work is done tell the mappers to terminate
    replicateM_ (length mappers) $ do
      them <- expect
      send them ()

  -- Start the mappers
  forM_ mappers $ \nid -> spawn nid ($(mkClosure 'mapperProcess) (master, workQueue, mrClosure))

  -- Wait for the partial results
  partials <- replicateM (Map.size input) expect

  -- We reduce on this node
  return (reducePerKey mr . groupByKey . concat $ partials)
