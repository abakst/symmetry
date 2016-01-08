{-# Language RebindableSyntax #-}
{-# Language TypeOperators    #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}

module PingMulti00 where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

{-
* Master
  PC 0: send worker-0 42
  PC 1: done

* Worker-i
  PC 0: (_ :: Int) <- receive
  PC 1: if (i < N - 1)
         then send worker-(i+1) 42
         else return ()
  PC 2: done
-}

-- send to a process that's in the same pid class
pingServer :: (DSL repr) => repr (Process repr ())
pingServer  = do (_ :: repr Int) <- recv
                 --if (i < N - 1)
                 --  then send worker-(i+1) 42
                 --  else return ()
                 ret tt

master :: (DSL repr) => repr (Process repr ())
master  = do r <- newRMulti
             ps <- spawnMany r (int 3) pingServer
             send (Symmetry.Language.lookup ps (int 0)) (int 42)
             ret tt

main :: IO ()
main = checkerMain (exec master)
