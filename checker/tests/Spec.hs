module Main where

import Symmetry.Language hiding (return)
import Symmetry.Verify
import Text.Printf

import Ping00
import SrcStutter
import SrcHelper hiding (print)

test_benchmark bmk name = do b <- checkerMain bmk
                             if b
                                then printf "Benchmark: %-20s => PASSED\n" name
                                else printf "Benchmark: %-20s => FAILED\n" name

main :: IO ()
main = do printf "\n"
          test_benchmark mainProc "Ping00"
          test_benchmark (exec (ret_tt stutter)) "Stutter"
          return ()

