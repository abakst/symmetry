module ConcDB where

import Text.Printf
import Control.Monad                    (forever)  
import Control.Distributed.Process
import Control.Distributed.Process.Node
import Network.Transport.TCP            (createTransport, defaultTCPParameters)
  
data DBMsg = Alloc Int Int
           | Lookup Int
           | Free
           | Allocated
             
{-
Gᵢ = ∀ c:client. c -> server<DBMsg>; server -> c<DBMsg>
G = μX. Gᵢ; X.
-}
 
main :: Int -> IO ()
main n = do
  Right t <- createTransport "127.0.0.1" "10501" defaultTCPParameters
  node <- newLocalNode t initRemoteTable
  forkProcess node $ do 
    db <- spawnLocal (database [])
    replicateM_ n (spawnLocal (client db))
  terminate

{-
G|server = μX. Gᵢ|server; X. 
         = μX. ∀ c:client. ?<c,DBMsg>.!<c,DBMsg>; X.
-}
database db = do
  receiveWait [\(Alloc k v, p) -> alloc k p
              ,\(Lookup k, p) -> lkup k p
              ]
    where
      alloc k p = case lookup k db of
                    Nothing -> do 
                      send p Free
                      database ((k,v) :: db)
                    _ -> do
                      send p Allocated
                      database db
      lkup k p = do 
         send p (lookup k db)
         database db
                  
readCmd = undefined

{-
G↑z:client = T(z) 
           = μX. (!<server, DBMSG>.?<server, DBMSG> | 
                ∀ y:client∖z.y -> server<DBMSG>;server->y<DBMSG>↑z:client); X
           = μX. (!<server, DBMSG>.?<server, DBMSG> | ε) ; X
           = μX. (!<server, DBMSG>.?<server, DBMSG>) ; X
-}
client db = do
  cmd <- liftIO readCmd
  case cmd of
    ("i", k) ->
      send db (Alloc k 0)
      receiveWait [\Free -> client db
                  ,\Allocated -> client db]
    ("l", k) ->
      send db (Lookup k)
      receiveWait [\Nothing -> client db
                  ,\Just _ -> client db]
  
   
