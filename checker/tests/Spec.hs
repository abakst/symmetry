module Main where

import Symmetry.Language hiding (return)
import Symmetry.Verify
import Text.Printf

import Ping00
--import PingMulti00
--import SrcConcDB :: AbsValToIL (Int, Pid RSing)
import SrcFiniteLeader
--import SrcFirewall
--import SrcHowait
--import SrcParikh
import SrcPipe
--import SrcReslock
--import SrcRing   :: Fresh [Int]
--import SrcSieve  :: Join
--import SrcStateFactory
import SrcStutter

import SrcHelper hiding (print)

test_benchmark bmk name = do b <- checkerMain bmk
                             if b
                                then printf "Benchmark: %-20s => PASSED\n" name
                                else printf "Benchmark: %-20s => FAILED\n" name

main :: IO ()
main = do printf "\n"
          test_benchmark mainProc "Ping"
          test_benchmark (exec (ret_tt stutter)) "Stutter"
          test_benchmark (exec (ret_tt finite_leader)) "Finite Leader"
          test_benchmark (exec (ret_tt pipe)) "Pipe"
          return ()

