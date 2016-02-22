module MapReduce where

import Text.Printf
import Control.Monad                    (forever)  
import Control.Distributed.Process
import Control.Distributed.Process.Node
import Network.Transport.TCP            (createTransport, defaultTCPParameters)
import Bootstrap                        (execProc)
  
data Message = Map | Reduce
             
{-
G = μX. ∀(c:client). s -> c<Map>; c -> s<Reduce>; X.
-}

main = execProc $ do
         self <- getSelfPid
         -- corresponds to:
         ps <- spawnMany n (client self)
         -- c∀(x:client).
         forM_ ps $ \p ->
           send p Reduce
         
 where
   n :: Int
   n = undefined
      
{-
G↑p = μX. ((s -> p<Map>. p -> s<Reduce>) ↑ p 
          | ∀ (c:client != p) (s -> c<Map>. c -> s<Reduce>) ↑ p); X
    = μX. ((?s<Map>. !s<Reduce>)
          | ∀ (c:client != p) ε); X
    = μX. ?s<Map>; !s<Reduce>; X
-} 
client server = 
  Map <- expect
  send server Reduce
