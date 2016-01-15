module SymMap where

import Data.Map.Strict
import Data.Maybe

--data Map_t k v = M (k -> v)

data Map_t k v = M (Map k v)

instance (Show a, Show b) => Show (Map_t a b) where
  show (M m) = show m

{-@ embed Map_t as Map_t @-}
{-@ measure Map_select :: Map_t k v -> k -> v @-}
{-@ measure Map_store :: Map_t k v -> k -> v -> Map_t k v @-}
 
{-@ get :: m:Map_t k v -> k:k -> {v:v | v = Map_select m k} @-}
get :: (Ord k, Show k, Show v) => Map_t k v -> k -> v
get (M m) k = fromMaybe (error ((show k) ++ " doesn't belong to " ++ (show m)))
                        (Data.Map.Strict.lookup k m)

{-@ put :: m:Map_t k v -> k:k -> v:v -> {vv:Map_t k v | vv = Map_store m k v } @-}
put :: (Ord k) => Map_t k v -> k -> v -> Map_t k v
put (M m) k v = M $ Data.Map.Strict.insert k v m

empty :: (Ord k) => Map_t k v
empty =  M $ Data.Map.Strict.empty
