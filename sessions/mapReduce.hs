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
         spawnMany (client self)
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
  Reduce <- expect
  send server Map
