module Main where

import System.Directory
import System.Exit
import System.Environment
import System.FilePath
import System.IO
import System.IO.Error
import System.Process
import Text.Printf
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Ingredients.Rerun
import Test.Tasty.Options
import Test.Tasty.Runners

testRunner = rerunningTests
               [ listingTests
               , consoleTestReporter
               ]

main :: IO ()
main = tests >>= run
  where
    run = defaultMainWithIngredients [
           testRunner
          ]
    tests = group "Tests" [ prologTests ]

quickCheckTests
  = group "QuickCheck" [
     testGroup "pos" <$> dirTests "checker/tests/pos" [] cmd ExitSuccess
    ]
  where
    cmd = "--qc --verify --qc-samples 25"

prologTests
  = group "Prolog Rewriter" [
     testGroup "benchmarks" <$> dirTests "checker/tests/benchmarks" [] cmd ExitSuccess
    ]
  where
    cmd = "--rewrite"

---------------------------------------------------------------------------
-- Nicked from LH:
---------------------------------------------------------------------------
group n xs = testGroup n <$> sequence xs

---------------------------------------------------------------------------
dirTests :: FilePath -> [FilePath] -> String -> ExitCode -> IO [TestTree]
---------------------------------------------------------------------------
dirTests root ignored testcmd code 
  = do files    <- walkDirectory root
       let tests = [ rel | f <- files, isTest f, let rel = makeRelative root f, rel `notElem` ignored ]
       return    $ mkTest testcmd code root <$> tests

---------------------------------------------------------------------------
mkTest :: String -> ExitCode -> FilePath -> FilePath -> TestTree
---------------------------------------------------------------------------
mkTest testcmd code dir file
  = testCase file $ do
      (_,_,_,ph) <- createProcess $ shell cmd
      c          <- waitForProcess ph
      assertEqual "Wrong exit code" code c
  where
    cmd = printf "cd %s && runghc %s %s" dir file testcmd

binPath pkgName = do
  testPath <- getExecutablePath
  return    $ (takeDirectory $ takeDirectory testPath) </> pkgName </> pkgName             

isTest   :: FilePath -> Bool
isTest f =  takeExtension f == ".hs"
         || takeExtension f == ".lhs"
----------------------------------------------------------------------------------------
walkDirectory :: FilePath -> IO [FilePath]
----------------------------------------------------------------------------------------
walkDirectory (r:_)
  | r == '.' = return []
walkDirectory root
  = do (ds,fs) <- partitionM doesDirectoryExist . candidates =<< (getDirectoryContents root `catchIOError` const (return []))
       (fs ++) <$> concatMapM walkDirectory ds
    where
       candidates fs = [root </> f | f <- fs, not (isExtSeparator (head f))]

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM f = go [] []
  where
    go ls rs []     = return (ls,rs)
    go ls rs (x:xs) = do b <- f x
                         if b then go (x:ls) rs xs
                              else go ls (x:rs) xs

concatMapM :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatMapM f []     = pure []
concatMapM f (x:xs) = (++) <$> f x <*> concatMapM f xs
