{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Symmetry.Verify where

import Symmetry.SymbEx
import Symmetry.IL.Render
import Symmetry.IL.AST

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

data MainOptions = MainOptions { optVerify  :: Bool
                               , optVerbose :: Bool
                               , optDir     :: String
                               }

instance Options MainOptions where
  defineOptions
    = MainOptions <$> simpleOption "verify" False "Run Verifier"
                  <*> simpleOption "verbose" False "Verbose Output"
                  <*> simpleOption "pmlfile" ".symcheck" "Directory to store intermediate results"

spinCmd :: FilePath -> CreateProcess
spinCmd f = shell ("spin -m -a " ++ f)

ccCmd :: CreateProcess
ccCmd     = shell ("cc -O3 -DSAFETY -DNOBOUNDCHECK -DNOCOMP -DSFH -DNOFAIR"
                   ++ " -o pan pan.c")

panCmd :: CreateProcess
panCmd    = shell "./pan -X -n -m1000000"

outName :: FilePath
outName = "out.pml"

outf, outTrail :: FilePath -> FilePath
outf d = d </> "out.pml"
outTrail d = outf d <.> "trail"

runCmd verb pre wd c
  = do (_,Just hout,Just herr,p) <- createProcess c { cwd = Just wd
                                                    , std_out = CreatePipe
                                                    , std_err = CreatePipe
                                                    }

       when verb $ do
         putStrLn pre
         output <- hGetContents hout
         when (output /= "") $ putStrLn output

       checkExit p herr

       when verb $ putStrLn "DONE"
  where
    checkExit x h = do e <- waitForProcess x
                       case e of
                         ExitSuccess -> return ()
                         _           -> do
                           putStrLn =<< hGetContents h
                           exitWith e


run1Cfg :: Bool -> FilePath -> Config () -> IO Bool
run1Cfg verb outd cfg
  = do createDirectoryIfMissing True outd
       removeFile (outTrail outd) `catch` \(_ :: IOException) ->
         return ()
       let cfgUnfold = unfold cfg
       renderToFile (outf outd) cfgUnfold
       runCmd verb "GENERATING SPIN MODEL:" outd (spinCmd outName)
       runCmd verb "COMPILING VERIFIER:" outd ccCmd
       runCmd verb "CHECKING MODEL:" outd panCmd
       fileExists (outTrail outd)
  where
    fileExists f = catch (openFile f ReadMode >> return True)
                         (\(_ :: IOException) -> return False)

checkerMain :: SymbEx () -> IO ()
checkerMain main
  = runCommand $ \opts _ ->
      if optVerify opts then
        do d <- getCurrentDirectory
           let  dir  = optDir opts
                verb = optVerbose opts
                cfgs = stateToConfigs . runSymb $ main
                outd = d </> dir
           es <- forM cfgs $ run1Cfg verb outd
           when (or es) exitFailure
           exitSuccess
      else
        exitSuccess
