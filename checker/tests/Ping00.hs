{-# Language ScopedTypeVariables #-}
<<<<<<< Updated upstream
{-# Language FlexibleContexts #-}
module Ping00 where
=======
{-# Language RebindableSyntax #-}
module Main where
>>>>>>> Stashed changes

import Prelude hiding ((>>=), (>>), fail, return)
import Symmetry.Language
import Symmetry.Verify

pingServer :: (CloudDSL repr) => repr (Process repr ())  
pingServer = do myPid <- self
                p     <- recv
                send p myPid

master :: forall repr.
          (CloudDSL repr)
       => repr (RSing -> Process repr ())
master = lam $ \r -> do p     <- spawn r pingServer
                        myPid <- self
                        _     <- send p myPid
                        _     <- recv :: repr (Process repr (Pid RSing))
                        return tt

mainProc :: (CloudDSL repr) => repr ()
mainProc = exec $ do r <- newRSing
                     r |> master 

-- main :: IO ()
-- main = checkerMain mainProc
