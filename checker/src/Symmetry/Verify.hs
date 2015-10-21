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
import System.Process (CreateProcess, createProcess, StdStream(..), cwd, std_out, proc, shell, waitForProcess)
import Text.Printf
import Options

data MainOptions = MainOptions { optVerify :: Bool
                               , optDir    :: String
                               }

instance Options MainOptions where
  defineOptions
    = MainOptions <$> simpleOption "verify" False "Run Verifier"
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

run1Cfg :: FilePath -> Config () -> IO Bool
run1Cfg outd cfg
  = do createDirectoryIfMissing True outd
       removeFile (outTrail outd) `catch` \(_ :: IOException) ->
         return ()
       renderToFile (outf outd) cfg
       runCmd (spinCmd outName)
       runCmd ccCmd
       runCmd panCmd
       fileExists (outTrail outd)
  where
    fileExists f = catch (openFile f ReadMode >> return True)
                         (\(_ :: IOException) -> return False)

    runCmd c    = do (_,_,_,x) <- createProcess c { cwd = Just outd, std_out = CreatePipe }
                     checkExit x

    checkExit x = do e <- waitForProcess x
                     case e of
                       ExitSuccess -> return ()
                       _           -> exitWith e

checkerMain :: SymbEx () -> IO ()
checkerMain main
  = runCommand $ \opts _ ->
      if optVerify opts then
        do d <- getCurrentDirectory
           let  dir  = optDir opts
                cfgs = stateToConfigs . runSymb $ main
                outd = d </> dir
           es <- forM cfgs $ run1Cfg outd
           when (or es) exitFailure
           exitSuccess
      else
        exitSuccess
