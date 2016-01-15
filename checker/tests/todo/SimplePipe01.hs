{-# Language RebindableSyntax #-}
{-# Language TypeOperators    #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}

module PingMulti01 where

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

-- send to a process that's in the same pid class
pingServer :: (DSL repr) => repr (Process repr ())
pingServer  = do (tmp :: repr ()) <- recv
                 ret tt

master :: (DSL repr) => repr (Process repr ())
master  = do r   <- newRMulti
             pids <- spawnMany r (int 2) pingServer
             doMany pids (lam $ \pid -> send pid tt)
             ret tt

main :: IO ()
main = checkerMain (exec master)
