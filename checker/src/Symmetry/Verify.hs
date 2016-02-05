{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Symmetry.Verify where

import Symmetry.SymbEx
import Symmetry.IL.Render.Horn
import Symmetry.IL.AST
-- import Symmetry.IL.Unfold
-- import Symmetry.IL.Inst
-- import Symmetry.IL.TrailParser

import System.Console.ANSI
import Paths_checker
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
import Text.PrettyPrint.Leijen  (pretty, nest, text, (<>), line, hPutDoc)
import qualified Data.Map.Strict as M

data MainOptions = MainOptions { optVerify  :: Bool
                               , optVerbose :: Bool
                               , optProcess :: Bool
                               , optModel   :: Bool
                               , optDir     :: String
                               }

instance Options MainOptions where
  defineOptions
    = MainOptions <$> simpleOption "verify" False "Run Verifier"
                  <*> simpleOption "verbose" False "Verbose Output"
                  <*> simpleOption "dump-process" False "Display Intermediate Process Description"
                  <*> simpleOption "dump-model" False "Dump Spin model"
                  <*> simpleOption "outdir" ".symcheck" "Directory to store intermediate results"

runChecker :: Config a
           -> FilePath
           -> IO ()
runChecker c fn
  = writeFile fn (renderSimulator c)

runQuickChecker :: Config a
                -> FilePath
                -> IO ()
runQuickChecker c fn
  = writeFile fn (renderQCFile c)

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
copyMapModule d
  = do f <- getDataFileName ("include" </> "SymMap.hs")
       copyFile f (d </> "SymMap.hs")

copyVectorModule d
  = do f <- getDataFileName ("include" </> "SymVector.hs")
       copyFile f (d </> "SymVector.hs")

run1Cfg :: MainOptions -> FilePath -> Config () -> IO Bool
run1Cfg opt outd cfg
  = do when (optModel opt) $ do
         createDirectoryIfMissing True outd
         copyMapModule    outd
         copyVectorModule outd
       if (optVerify opt) then do
         runChecker cfg (outd </> "SymVerify.hs")
         runQuickChecker cfg (outd </> "QC.hs")
         return True
       else
         return True
  where
    verb = optVerbose opt
    fileExists f = catch (openFile f ReadMode >> return True)
                         (\(_ :: IOException) -> return False)
    filterBoundedAbs c@(Config { cSets = bs }) =
      c { cProcs = [ p | p <- cProcs c, not (isBounded bs (fst p)) ] }


report status
  = if not status then
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

      when (optProcess opts) .
        forM_ cfgs $ \c ->
          print $ text "Config" <> nest 2 (line <> pretty c)

      d <- getCurrentDirectory

      let  dir  = optDir opts
           outd = d </> dir
           optsImplied = opts { optModel = optModel opts ||
                                           optVerify opts }

      es <- forM cfgs $ run1Cfg optsImplied outd
      let status = and es
      report status
      unless status exitFailure

      exitSuccess

    where
      cfgs = stateToConfigs . runSymb $ main

outTrace = "/tmp/trace"

spinTrailCmd  :: String -> CreateProcess
spinTrailCmd f = shell ("spin -p -t " ++ f ++
                        "| sed '/:init:/d' " ++
                        "| grep -E '^[[:space:]]*[[:digit:]]+:' >" ++ outTrace)


type IdStmtMap = M.Map Int (Stmt Int)

flattenStmt                     :: Stmt a -> [Stmt a]
flattenStmt s@(SBlock l _)       = s : (concatMap flattenStmt l)
flattenStmt s@(SIter _ _ s' _)   = s : (flattenStmt s')
flattenStmt s@(SLoop _ s' _)     = s : (flattenStmt s')
flattenStmt s@(SChoose _ _ s' _) = s : (flattenStmt s')
flattenStmt s@(SCase _ _ _ sl sr _)  = s : (concatMap flattenStmt [sl,sr])
flattenStmt s@(SNonDet l _)      = s : (concatMap flattenStmt l)
flattenStmt s                    = [s]

buildIdStmtMap                         :: Config Int -> IdStmtMap
buildIdStmtMap (Config { cProcs = ps }) =
  let pairs = [ (annot s,s) | (pid,main_s) <- ps, s <- (flattenStmt main_s) ]
   in M.fromList pairs

dangerZone str =
  do setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
     putStr str
     setSGR [Reset]
     putStr "\n"
