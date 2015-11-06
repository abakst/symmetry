{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Symmetry.Verify where

import Symmetry.SymbEx
import Symmetry.IL.Render
import Symmetry.IL.AST

import System.Console.ANSI
import Control.Exception
import Control.Monad
import Control.Applicative
import System.Exit
import System.Directory
import System.FilePath
import System.IO
import System.Process hiding (runCommand)
import Text.Printf
import Options
import Text.PrettyPrint.Leijen  (pretty, nest, text, (<>), line)

data MainOptions = MainOptions { optVerify  :: Bool
                               , optBounded :: Int
                               , optVerbose :: Bool
                               , optProcess :: Bool
                               , optDir     :: String
                               }

instance Options MainOptions where
  defineOptions
    = MainOptions <$> simpleOption "verify" False "Run Verifier"
                  <*> simpleOption "set-size" 0 "Concrete set size"
                  <*> simpleOption "verbose" False "Verbose Output"
                  <*> simpleOption "dump-process" False "Display Intermediate Process Description"
                  <*> simpleOption "pmlfile" ".symcheck" "Directory to store intermediate results"

spinCmd :: FilePath -> CreateProcess
spinCmd f = shell ("spin -m -a " ++ f)

ccCmd :: CreateProcess
ccCmd     = shell ("cc -O2 -DVECTORSZ=2048 -DSAFETY -DNOBOUNDCHECK -DNOCOMP -DSFH -DNOFAIR"
                   ++ " -o pan pan.c")

panCmd :: CreateProcess
panCmd    = shell "./pan -X -n -m1000000"

outName :: FilePath
outName = "out.pml"

outf, outTrail :: FilePath -> FilePath
outf d = d </> "out.pml"
outTrail d = outf d <.> "trail"

runCmd               :: Bool -> String -> FilePath -> CreateProcess -> IO ()
runCmd verb pre wd c
  = do (_,Just hout,Just herr,p) <- createProcess c { cwd = Just wd
                                                    , std_out = CreatePipe
                                                    , std_err = CreatePipe
                                                    }

       when verb $ do
         setSGR [SetConsoleIntensity FaintIntensity]
         putStr (pre ++ "...")
         output <- hGetContents hout
         when (output /= "") $
           putStr ("\n" ++ output)
         setSGR [Reset]

       checkExit p herr

       when verb $ do
         setSGR [SetConsoleIntensity FaintIntensity]
         putStr "DONE.\n"
         setSGR [Reset]
  where
    checkExit x h = do e <- waitForProcess x
                       case e of
                         ExitSuccess -> return ()
                         _           -> do
                           putStrLn =<< hGetContents h
                           exitWith (ExitFailure 126)


run1Cfg :: MainOptions -> FilePath -> Config () -> IO Bool
run1Cfg opt outd cfg
  = do createDirectoryIfMissing True outd
       removeFile (outTrail outd) `catch` \(_ :: IOException) ->
         return ()
       let cfgOut = if setsz > 0 then
                      boundAbs setsz cfg
                    else
                      unfoldAbs cfg
       renderToFile (outf outd) cfgOut
       runCmd verb "GENERATING SPIN MODEL:" outd (spinCmd outName)
       runCmd verb "COMPILING VERIFIER:" outd ccCmd
       runCmd verb "CHECKING MODEL:" outd panCmd
       failure <- fileExists (outTrail outd)
       let unfolded = filterBoundedAbs . freshIds . instAbs $ unfold cfgOut
       when failure (printTrace verb outd unfolded)
       return failure
  where
    verb = optVerbose opt
    setsz = optBounded opt
    fileExists f = catch (openFile f ReadMode >> return True)
                         (\(_ :: IOException) -> return False)
    filterBoundedAbs c@(Config { cSets = bs }) =
      c { cProcs = [ p | p <- cProcs c, not (isBounded bs (fst p)) ] }


report status
  = if status then
      do setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
         putStr "UNSAFE"
         setSGR [Reset]
         putStr "\n"
    else
      do setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Green]
         putStr "SAFE"
         setSGR [Reset]
         putStr "\n"

checkerMain :: SymbEx () -> IO ()
checkerMain main
  = runCommand $ \opts _ -> do

      when (optProcess opts) $
        forM_ cfgs $ \c ->
          print $ text "Config" <> nest 2 (line <> pretty c)

      when (optVerify opts) $ do
        d <- getCurrentDirectory
        let  dir  = optDir opts
             verb = optVerbose opts
             outd = d </> dir
        es <- forM cfgs $ run1Cfg opts outd
        let status = or es
        report status
        when status exitFailure

      exitSuccess

    where
      cfgs = stateToConfigs . runSymb $ main

spinTrailCmd  :: String -> CreateProcess
spinTrailCmd f = shell ("spin -p -t " ++ f ++
                        "| sed '/Error/Q' | sed '/:init:/d' " ++
                        "| grep -P '^\\s*\\d+:' > /tmp/trace")

printTrace           :: Bool -> FilePath -> Config Int -> IO ()
printTrace verb outd c = do let pml = outf outd
                            runCmd verb "RE-RUNNING THE TRACE:" outd $ spinTrailCmd pml
