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

-- | API
main :: Int -> IO ()
main n = execProc {- < μX. ∀p. p --> db<...>; db --> p; X > -} mainProc
    where 
      {- mainProc :: Process me [] < me ▹ ε
                                   | db ▹ μX. (TDb p p p p); X 
                                   | p  ▸ μX. (TClient db); X   
                                   > 
                                   ()
       -}
      mainProc = do
        db <- spawnLocal (database [])
        loop db n
      {- loop :: Process me < me ▹ ε
                            | p  ▸ ...μX. (TClient db); X... > -}
      loop _ 0 = return ()
      loop db n = do
        spawnLocal (client db)
        loop db (n - 1)
        -- replicateM_ n (spawnLocal (client db))
  -- do
  -- Right t <- createTransport "127.0.0.1" "10501" defaultTCPParameters
  -- node <- newLocalNode t initRemoteTable
  -- forkProcess node $ do 
  --   db <- spawnLocal (database [])
  --   replicateM_ n (spawnLocal (client db))
  -- terminate

{-
Process me < me ▹ μX. ∀abcd. 
                      { recv(a, (Alloc k v, b)); { send(b, Free)
                                                 , send(b, Allocated)
                                                 }
                      , recv(c, (Lookup k, d)); send(d, Maybe Int)
                      }; X > ()
-}
database db = do
  -- ?<p, {Alloc k v <p>, Lookup k<p>}>; !<c,{DBMsg, Maybe Int}>; X
  receiveWait [\Alloc k v, p) -> alloc k p
              ,\(Lookup k, p) -> lkup k p
              ]
    where
      alloc k p = 
        -- !<p, {Free, Allocated}>
        case lookup k db of
          Nothing -> do 
                -- !<p, Free>
                send p Free
                -- X
                database ((k,v) : db)
          _ -> do
                -- !<p, Allocated>
                send p Allocated
                -- X
                database db

      lkup k p = do 
         -- !<p, Maybe Int>
         send p (lookup k db)
         -- X
         database db
                  
readCmd = undefined

{-
db:Pid ->
Process me [a, b, c] < me ▹ μX. { send(db, (Alloc k v, me)); { recv(a, Free)
                                                             , recv(b, Allocated)
                                                             }; X
                                , send(db, (Lookup k, me)); recv(c, Maybe Int)
                                }; X > ()
-}
client db = do
  cmd <- liftIO readCmd
  self <- getSelfPid
  case cmd of
    ("i", k) ->
      -- !<db, Alloc k v>
      send db (Alloc k 0, self)
      -- ?<db, {Free, Allocated}>
      receiveWait [\Free -> client db
                  ,\Allocated -> client db]
    ("l", k) ->
      -- !<db, Lookup<self>>
      send db (Lookup k, self)
      -- ?<db, {Maybe|isNothing, Just|~isNothing}>
      receiveWait [\Nothing -> client db
                  ,\Just _ -> client db]
  
   
