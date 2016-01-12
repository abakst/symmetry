{-# Language RebindableSyntax #-}
{-# Language TypeOperators    #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}

module PingMulti00 where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

-- send to a process that's in the same pid class
pingServer :: (DSL repr) => repr (Process repr ())
pingServer  = do (tmp :: repr ()) <- recv
                 ret tt

master :: (DSL repr) => repr (Process repr ())
master  = do s   <- newRSing
             pid <- spawn s pingServer
             send pid tt

main :: IO ()
main = checkerMain (exec master)
