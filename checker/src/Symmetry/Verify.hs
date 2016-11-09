{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Symmetry.Verify where

import Symmetry.SymbEx
import Symmetry.IL.AST
import Symmetry.IL.Rewrite.Prolog

import System.Console.ANSI
import Paths_checker
import Control.Monad
import System.Exit
import System.Directory
import System.FilePath
import System.IO
import GHC.IO.Handle
import GHC.IO.Device
import System.Process hiding (runCommand)
import Text.Printf
import Options
import Text.PrettyPrint.Leijen  (pretty, nest, text, (<>), line)
import qualified Data.Map.Strict as M

data MainOptions = MainOptions { optVerify  :: Bool
                               , optRewrite  :: Bool
                               , optQC      :: Bool
                               , optQCSamples :: Int
                               , optVerbose :: Bool
                               , optProcess :: Bool
                               , optDir     :: String
                               , optModel   :: Bool
                               , optQuiet   :: Bool
                               }

instance Options MainOptions where
  defineOptions
    = MainOptions <$> simpleOption "verify" False "Run Verifier"
                  <*> simpleOption "rewrite" False "Dump Prolog version of protocol suitable for rewriting"
                  <*> simpleOption "qc" False "Run QuickCheck instead of Verifier"
                  <*> simpleOption "qc-samples" 1000 "Number of random initial states to explore"
                  <*> simpleOption "verbose" False "Verbose Output"
                  <*> simpleOption "dump-process" False "Display Intermediate Process Description"
                  <*> simpleOption "outdir" ".symcheck" "Directory to store intermediate results"
                  <*> simpleOption "dump-model" False "<disabled>"
                  <*> simpleOption "quiet" False "Don't print result"

runCmd               :: Bool -> String -> FilePath -> CreateProcess -> IO Bool
runCmd verb pre wd c
  = do hStdOut <- if verb then return CreatePipe else UseHandle <$> openFile "/dev/null" WriteMode
       
       (_,hout,Just herr,p) <- createProcess c { cwd = Just wd
                                                    , std_out = hStdOut
                                                    , std_err = CreatePipe
                                                    }
       when verb $ do
         setSGR [SetConsoleIntensity FaintIntensity]
         putStr (pre ++ "...")
         let Just hout' = hout
         output <- hGetContents hout'
         when (output /= "") $
           putStr ("\n" ++ output)

       b      <- checkExit p herr

       when verb $ do
         setSGR [Reset]
         setSGR [SetConsoleIntensity FaintIntensity]
         putStr "DONE.\n"
         setSGR [Reset]

       return b
  where
    checkExit x h = do e <- waitForProcess x
                       putStrLn =<< hGetContents h
                       putStrLn (show e)
                       return (e == ExitSuccess)
-- copyMapModule opt d
--   = do let f' = if optQC opt
--                    then "SymMapQC.hs"
--                    else "SymMap.hs"
--        f <- getDataFileName ("checker" </> "include" </> f')
--        copyFile f (d </> "SymMap.hs")

-- copyVectorModule opt d
--   = do
--        let f' = if optQC opt
--                    then "SymVectorQC.hs"
--                    else "SymVector.hs"
--        f <- getDataFileName ("checker" </> "include" </> f')
--        copyFile f (d </> "SymVector.hs")

-- copyBoilerModule opt d
--   = do
--        let f' = if optQC opt
--                    then "SymBoilerPlateQC.hs"
--                    else "SymBoilerPlate.hs"
--        f <- getDataFileName ("checker" </> "include" </> f')
--        copyFile f (d </> "SymBoilerPlate.hs")

-- copyWeb _ d
--   = forM_ ["states.js", "states.html"] $ \f -> 
--        do f' <- fn f
--           copyFile f' (d </> f)
--   where
--     fn f = getDataFileName ("checker" </> "include" </> f)

-- copyIncludes opt d =
--   mapM_ (\f -> f opt d) [ copyMapModule
--                         , copyVectorModule
--                         , copyBoilerModule
--                         , copyWeb
--                         ]


copyPrologFiles :: FilePath -> IO ()
copyPrologFiles d =
  forM_ ["rewrite.pl", "tags.pl", "lib/misc.pl"] $ \f ->
    do f' <- getDataFileName ("rewrites" </> "src" </> f)
       copyFile f' (d </> f)

runLiquid :: Bool -> FilePath -> FilePath -> IO Bool
runLiquid verb fp cwd
  = runCmd verb "Running Verifier" cwd cmd
  where
    cmd = shell (printf "liquid %s" fp)

runQC :: Bool -> FilePath -> FilePath -> IO Bool
runQC verb fp cwd
  = runCmd verb "Running QuickCheck" cwd cmd
  where
    cmd = shell (printf "runghc %s" fp)

runProlog :: Bool -> FilePath -> IO Bool
runProlog verb cwd
  = runCmd verb "Running Rewriter" cwd cmd
  where
    cmdStr = "sicstus --noinfo --nologo --goal \"main,halt.\" -l symverify.pl"
    cmd    = shell cmdStr

runVerifier opt outd
 | optVerify opt && optQC opt =
    runQC (optVerbose opt) (outd </> "QC.hs") outd
 | optVerify opt =
    runLiquid (optVerbose opt) (outd </> "SymVerify.hs") outd
 | optRewrite opt
   = runProlog (optVerbose opt) outd
 | otherwise = return True
  

run1Cfg :: MainOptions -> FilePath -> Config () -> IO Bool
run1Cfg opt outd cfg
  = do when (optProcess opt) $
         pprint cfg

       when (optRewrite opt) $ do
         createDirectoryIfMissing True outd
         createDirectoryIfMissing True (outd </> "lib")
         copyPrologFiles outd
         writeFile (outd </> "symverify.pl") p

       runVerifier opt outd
  where
    p        = printProlog cfg
    pprint c = print $
               text "Config" <>
               nest 2 (line  <> pretty c)


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
           optsImplied = opts { optModel = optModel opts
                                           {- || optVerify opts -} }

      es <- forM cfgs $ run1Cfg optsImplied outd
      let status = and es

      when (not (optQuiet opts)) $ report status

      unless status exitFailure
      exitSuccess
    where
      cfgs = stateToConfigs . runSymb $ main

type IdStmtMap = M.Map Int (Stmt Int)

flattenStmt                     :: Stmt a -> [Stmt a]
flattenStmt s@(Block l _)       = s : (concatMap flattenStmt l)
flattenStmt s@(Iter _ _ s' _)   = s : (flattenStmt s')
flattenStmt s@(Loop _ _ s' _)   = s : (flattenStmt s')
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
