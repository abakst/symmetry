{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Symmetry.Verify where

import Symmetry.SymbEx
import Symmetry.IL.Render
import Symmetry.IL.AST
import Symmetry.IL.Unfold
import Symmetry.IL.Inst
import Symmetry.IL.TrailParser

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
import qualified Data.Map.Strict as M

data MainOptions = MainOptions { optVerify  :: Bool
                               , optVerbose :: Bool
                               , optProcess :: Bool
                               , optModel   :: Bool
                               , optDir     :: String
                               , optName    :: String
                               , optInfty   :: Int
                               , optWorker  :: Int
                               , optJob     :: Int
                               }

instance Options MainOptions where
  defineOptions
    = MainOptions <$> simpleOption "verify" False "Run Verifier"
                  <*> simpleOption "verbose" False "Verbose Output"
                  <*> simpleOption "dump-process" False "Display Intermediate Process Description"
                  <*> simpleOption "dump-model" False "Dump Spin model"
                  <*> simpleOption "pmlfile" ".symcheck" "Directory to store intermediate results"
                  <*> simpleOption "name" "" "Name of the benchmark"
                  <*> simpleOption "infty" 3 "Max buffer length"
                  <*> simpleOption "worker" 3 "number of workers in the system"
                  <*> simpleOption "job" 3 "number of jobs in the system"

workerCount :: IO Int
workerCount =  runCommand $ \opts args -> return $ (optWorker opts)

jobCount :: IO Int
jobCount =  runCommand $ \opts args -> return (optJob opts)

spinCmd :: FilePath -> MainOptions -> CreateProcess
spinCmd f opt = shell (printf "spin -D__K__=%d -m -a %s" (optInfty opt) f)

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
  = do when (optModel opt) $
         createDirectoryIfMissing True outd
       when (optVerify opt) $ 
         removeFile (outTrail outd) `catch` \(_ :: IOException) ->
           return ()

       let cfgOut = unfoldAbs cfg

       when (optModel opt) $ do
         renderToFile (outf outd) cfgOut

       when (optVerify opt) $ do 
         runCmd verb "GENERATING SPIN MODEL:" outd (spinCmd outName opt)
         runCmd verb "COMPILING VERIFIER:" outd ccCmd
         runCmd verb "CHECKING MODEL:" outd panCmd

       if (optVerify opt) then
         do failure <- fileExists (outTrail outd)
            let unfolded = filterBoundedAbs . freshIds . instAbs $ unfold cfgOut
            when failure (printTrace verb outd unfolded)
            return $ not failure
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

      let  name = optName opts
           dir  = if   null name
                  then optDir opts
                  else optDir opts <.> name
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
flattenStmt s@(SCase _ sl sr _)  = s : (concatMap flattenStmt [sl,sr])
flattenStmt s@(SNonDet l _)      = s : (concatMap flattenStmt l)
flattenStmt s                    = [s]

buildIdStmtMap                         :: Config Int -> IdStmtMap
buildIdStmtMap (Config { cProcs = ps }) =
  let pairs = [ (annot s,s) | (pid,main_s) <- ps, s <- (flattenStmt main_s) ]
   in M.fromList pairs

printTrace            :: Bool -> FilePath -> Config Int -> IO ()
printTrace verb outd c = do let pml = outf outd
                            runCmd verb "RE-RUNNING THE TRACE:" outd $ spinTrailCmd pml
                            ts <- readTrails outTrace
                            let idStmtMap = buildIdStmtMap c
                            let getS m t = M.findWithDefault (SNull (-1)) (stmtId t) m
                            dangerZone "Counter Example:"
                            let tnss = map (\t -> (procId t, getS idStmtMap t)) ts
                            forM_ (zip [1..] tnss) (print . error_print_helper)

dangerZone str =
  do setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
     putStr str
     setSGR [Reset]
     putStr "\n"
