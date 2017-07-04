{-# Language RebindableSyntax #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
module Loop00 where

import Prelude hiding ((>>=), return, (>>), fail)
import Symmetry.Verify
import Symmetry.Language

bloo :: (DSL repr) => repr ((() -> Process repr ()) -> () -> Process repr ())
bloo = lam (\f -> (lam (\_ -> do y <- recv
                                 y |> f)))

blab :: (DSL repr) => repr (() -> Process repr ())
blab = fixM bloo

main :: IO ()
main = checkerMain (exec (tt |> blab))
