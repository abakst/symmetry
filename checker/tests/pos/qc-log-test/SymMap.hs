module SymMap where

import Data.Maybe
import Data.Map.Strict as Map

data Map_t k v = M (Map k v)
{-@ embed Map_t as Map_t @-}
{-@ measure Map_select :: Map_t k v -> k -> v @-}
{-@ measure Map_store :: Map_t k v -> k -> v -> Map_t k v @-}
 
{-@ get :: m:Map_t k v -> k:k -> {v:v | v = Map_select m k} @-}
get :: (Ord k) => Map_t k v -> k -> v
get (M m) k = let v = Map.lookup k m
              in if isJust v
                    then fromJust v
                    else error "No key found in map"

{-@ put :: m:Map_t k v -> k:k -> v:v -> {vv:Map_t k v | vv = Map_store m k v } @-}
put :: (Ord k) => Map_t k v -> k -> v -> Map_t k v
put (M m) k v = M (Map.insert k v m)
