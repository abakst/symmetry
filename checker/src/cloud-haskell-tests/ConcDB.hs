{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}

module ConcDB where

import Prelude hiding (lookup, read)
import TestMain
import Helper
import AST hiding (Process)
import Render

import Control.Distributed.Process
import Control.Distributed.Process.Serializable

import Data.Binary
import Data.Generics hiding (Generic)
import GHC.Generics
import GHC.Int

data AllocM = Alloc PeanoN ProcessId
              deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary AllocM

data FreeM = Free
             deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary FreeM

data AllocatedM = Allocated
                  deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary AllocatedM

data ValueM = Value PeanoN ProcessId
              deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary ValueM

data LookupM = Lookup PeanoN ProcessId
               deriving (Ord, Eq, Show, Typeable, Generic)
instance Binary LookupM

concdb_main :: Process ()
concdb_main  = do db <- spawnLocal (database [])
                  spawnmany (client db)

spawnmany   :: Process () -> Process ()
spawnmany f  = do spawnLocal f
                  b <- any_bool
                  if b
                     then spawnmany f
                     else return ()


database  :: [(PeanoN, PeanoN)] -> Process ()
database l = receiveWait [match allocHandler, match lookupHandler]
             where allocHandler (Alloc key p) =
                     case lookup key l of
                       Nothing  -> do send p Free
                                      let pred (Value v' p')    = p == p'
                                          handler (Value v' p') = database ((key,v'):l)
                                       in receiveWait [matchIf pred handler]
                       (Just _) -> send p Allocated >> database l
                   lookupHandler (Lookup key p) = send p (lookup key l) >> database l

lookup    :: Eq a1 => a1 -> [(a1, a)] -> Maybe a
lookup k l = case l of
               []         -> Nothing
               (k',v'):l' -> if k == k'
                                then (Just v')
                                else lookup k l'

client    :: ProcessId -> Process ()
client db  = do choice <- read
                self   <- getSelfPid
                case choice of
                  Ok_I -> do k <- any_nat
                             send db (Alloc k self)
                             say $ "adding " ++ (show k) ++ "?"
                             receiveWait [match freeHandler, match allocatedHandler]
                             where freeHandler Free = do v <- any_nat
                                                         send db (Value v self)
                                                         say $ "free! set it to " ++ (show v)
                                                         client db
                                   allocatedHandler Allocated = say "uups :(" >> client db
                  Ok_L -> do k <- any_nat
                             say $ "looking up for " ++ (show k)
                             send db (Lookup k self)
                             msg <- expect :: Process (Maybe PeanoN)
                             case msg of
                               Nothing   -> say "doesn't exists :("    >> client db
                               (Just v') -> say ("it's " ++ (show v')) >> client db

data MyChoice = Ok_I | Ok_L
read = do b <- any_bool
          return (if b then Ok_I else Ok_L)
