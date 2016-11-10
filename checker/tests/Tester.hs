#!/usr/bin/env stack
-- stack runghc --package directory --package filepath

{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Monad
import Data.List
import System.Directory
import System.FilePath.Posix
import Text.Printf
import System.Exit
import System.Process  
import qualified Options as O

data Benchmark = B { filename :: String, varname :: String }

pos_benchmarks :: [Benchmark]
pos_benchmarks =
  [ B "PingMulti00"      "pmzero"
  , B "PingMulti02"      "pmtwo"
  , B "PingMulti03"      "pmthree"
  , B "PingMulti2Party"  "pmtwoparty"
  , B "PingMultiSize"    "pmsize"
  
  , B "ConcDB"           "concdb"
  , B "DatabaseSample"   "dbsample"
  , B "Firewall"         "firewall"
  , B "MapReduce"        "mapreduce"
  , B "Parikh"           "parikh"
  , B "Registry"         "registry"
  , B "WorkStealing"     "ws"
  ]

neg_benchmarks :: [Benchmark]
neg_benchmarks =
  [ B "MapReduce01"  "mapreduce-err-01"
  , B "MapReduce02"  "mapreduce-err-02"
  , B "MapReduce03"  "mapreduce-err-03"
  , B "MapReduce04"  "mapreduce-err-04"
  , B "MapReduce05"  "mapreduce-err-05"

  , B "Firewall"     "firewall-err-01"
  , B "PingMulti"    "pingmulti-err-01"
  , B "WorkStealing" "ws-err-01"
  ]

data BenchmarkSuite = BS { suite      :: FilePath
                         , benchmarks :: [Benchmark]
                         , expected   :: ExitCode
                         }

benchmark_suite = [ BS "pos" pos_benchmarks ExitSuccess
                  , BS "neg-benchmarks" neg_benchmarks (ExitFailure 1)
                  ]

parse_time :: MainOptions -> BenchmarkSuite -> Benchmark -> IO ()
parse_time opts bs@BS{..} bmk@B{..}= do
  rootDir <- getCurrentDirectory >>= makeAbsolute

  let f         = printf "%s.hs" filename
      time_arg  = "%U"          -- only get the wall clock time
      exec      = "/usr/bin/time"
      args      = ["-f", time_arg] ++ ["stack", "runghc", "--", f, "--rewrite" ]
      std_in    = ""
      process   = (proc exec args){ cwd = Just (rootDir </> suite) }

  (ec, out, err) <- readCreateProcessWithExitCode process std_in

  let time = read (last $ lines err)

  printRow (optTable opts) bmk (toResult ec expected) time

-- -----------------------------------------------------------------------------
-- formatting
-- -----------------------------------------------------------------------------

data RowFormat = Latex | Regular
               deriving (Show)

data BenchmarkResult = Pass | Fail
                     deriving (Show)

toResult res exp = if res == exp then Pass else Fail

printRow :: RowFormat -> Benchmark -> BenchmarkResult -> Double -> IO ()

printRow Latex (B{..}) res time =   
  undefined

printRow Regular (B{..}) res time =   
  printf "%4s %-20s %g\n" (toErr res) (filename ++ ":") time
  where
    toErr Pass = ""
    toErr Fail = "FAIL"

-- -----------------------------------------------------------------------------
-- argument parsing
-- -----------------------------------------------------------------------------

rowFormatOptionType = O.optionType "RowFormat" Regular parser show
  where
    parser str = case str of
                   "latex"   -> Right Latex
                   "regular" -> Right Regular
                   _         -> Left str


instance O.Options MainOptions where
  defineOptions
    = MainOptions <$> O.defineOption rowFormatOptionType opts
    where
      opts o = o { O.optionLongFlags  = ["table"]
                 , O.optionShortFlags = ['t']
                 , O.optionDefault    = Regular
                 }

-- -----------------------------------------------------------------------------
-- main
-- -----------------------------------------------------------------------------

data MainOptions = MainOptions { optTable :: RowFormat }

runSuite opts bs@BS{..} = do
  rootDir <- getCurrentDirectory >>= makeAbsolute
  printf "-- %s ------------------------------\n" suite
  forM_ benchmarks (parse_time opts bs)
  return ()

runBenchmark opts BS{..} B{..} = undefined

main = O.runCommand $ \ opts _ -> forM_ benchmark_suite (runSuite opts) 
      
                           

