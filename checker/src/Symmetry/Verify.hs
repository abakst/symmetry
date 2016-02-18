{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Symmetry.Verify where

import Symmetry.SymbEx
import Symmetry.IL.AST
import Symmetry.IL.Model (generateModel)
import Symmetry.IL.ConfigInfo
import Symmetry.IL.Model.HaskellModel (printHaskell,printQCFile)
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
                               , optQC      :: Bool
                               , optVerbose :: Bool
                               , optProcess :: Bool
                               , optModel   :: Bool
                               , optDir     :: String
                               }

instance Options MainOptions where
  defineOptions
    = MainOptions <$> simpleOption "verify" False "Run Verifier"
                  <*> simpleOption "qc" False "Run QuickCheck instead of Verifier"
                  <*> simpleOption "verbose" False "Verbose Output"
                  <*> simpleOption "dump-process" False "Display Intermediate Process Description"
                  <*> simpleOption "dump-model" False "Dump Liquid Haskell model"
                  <*> simpleOption "outdir" ".symcheck" "Directory to store intermediate results"

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
copyMapModule opt d
  = do let f' = if optQC opt
                   then "SymMapQC.hs"
                   else "SymMap.hs"
       f <- getDataFileName ("include" </> f')
       copyFile f (d </> "SymMap.hs")

copyVectorModule opt d
  = do
       let f' = if optQC opt
                   then "SymVectorQC.hs"
                   else "SymVector.hs"
       f <- getDataFileName ("include" </> f')
       copyFile f (d </> "SymVector.hs")

copyBoilerModule opt d
  = do
       let f' = if optQC opt
                   then "SymBoilerPlateQC.hs"
                   else "SymBoilerPlate.hs"
       f <- getDataFileName ("include" </> f')
       copyFile f (d </> "SymBoilerPlate.hs")

copyIncludes opt d =
  mapM_ (\f -> f opt d) [ copyMapModule
                        , copyVectorModule
                        , copyBoilerModule ]

runLiquid :: FilePath -> FilePath -> IO () 
runLiquid fp cwd
  = runCmd True "Running Verifier" cwd cmd
  where
    cmd = shell (printf "liquid %s" fp)

runQC :: FilePath -> FilePath -> IO ()
runQC fp cwd
  = runCmd True "Running QuickCheck" cwd cmd
  where
    cmd = shell (printf "runghc %s" fp)

run1Cfg :: MainOptions -> FilePath -> Config () -> IO Bool
run1Cfg opt outd cfg
  = do when (optProcess opt) $
         pprint (config cinfo)

       when (optModel opt) $ do
         createDirectoryIfMissing True outd
         copyIncludes opt outd
         writeFile (outd </> "SymVerify.hs") f
         when (optQC opt)
              (writeFile (outd </> "QC.hs") (printQCFile cinfo' m))

       when (optVerify opt) $
            if optQC opt then
              runQC (outd </> "QC.hs") outd
            else
              runLiquid (outd </> "SymVerify.hs") outd
       return True
  where
    cinfo :: ConfigInfo (PredAnnot Int)
    (cinfo, m) = generateModel cfg
    cinfo'     = cinfo {isQC = optQC opt}
    f          = printHaskell cinfo' m
    pprint c = print $
               text "Config" <>
               nest 2 (line  <> pretty c)
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

type IdStmtMap = M.Map Int (Stmt Int)

flattenStmt                     :: Stmt a -> [Stmt a]
flattenStmt s@(Block l _)       = s : (concatMap flattenStmt l)
flattenStmt s@(Iter _ _ s' _)   = s : (flattenStmt s')
flattenStmt s@(Loop _ s' _)     = s : (flattenStmt s')
flattenStmt s@(Choose _ _ s' _) = s : (flattenStmt s')
flattenStmt s@(Case _ _ _ sl sr _)  = s : (concatMap flattenStmt [sl,sr])
flattenStmt s@(NonDet l _)      = s : (concatMap flattenStmt l)
flattenStmt s                    = [s]

buildIdStmtMap                         :: Config Int -> IdStmtMap
buildIdStmtMap (Config { cProcs = ps }) =
  let pairs = [ (annot s,s) | (pid,main_s) <- ps, s <- (flattenStmt main_s) ]
   in M.fromList pairs

dangerZone :: String -> IO ()
dangerZone str =
  do setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
     putStr str
     setSGR [Reset]
     putStr "\n"
