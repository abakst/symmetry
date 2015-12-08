module Symmetry.IL.SyncLoops where

import           Data.List
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.Query.Dominators
import           Data.Graph.Inductive.PatriciaTree
import qualified Data.Map.Strict as M
import           Symmetry.IL.AST
import           Data.Typeable
import           Data.Generics

stmtDoms :: Stmt Int
         -> Stmt Int
         -> [Stmt Int]
stmtDoms p s
  = case lookup (annot p) (dom graph (annot s)) of
      Just js -> listify ((`elem` js) . annot) s
      _       -> []
  where
    graph :: UGr
    graph = mkGraph (zip vs (repeat ())) es
    cfg   = nextStmts s
    vs = nub $ M.foldrWithKey (\k v a -> (k:v) ++ a) [] cfg -- zip (M.keys cfg) (repeat ())
    es = [ (i,j,()) | (i, js) <- M.toList cfg, j <- js ]
