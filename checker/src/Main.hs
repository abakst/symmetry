module Main where

import System.Eval.Haskell
import System.Environment
import System.Directory
import System.Console.GetOpt
import Control.Monad
import System.FilePath.Posix
import Text.PrettyPrint.Leijen hiding ((</>))

import Render
import AST

opts = [Option "f" ["file"] (ReqArg id "FILE") "Input File"]

main :: IO ()
main = do
  args <- getArgs
  case getOpt RequireOrder opts args of
    ([fn], _, _) -> do
         s <- readFile fn
         case read s :: Config () of
           c -> putDoc $ render c
           _ -> return ()

{-
:
:619.559.8000
:
-}
