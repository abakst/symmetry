{-# Language RebindableSyntax #-}
{-# Language TypeOperators #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module PingMulti00 where

import Prelude hiding (lookup, (>>=), (>>), fail, return) 
import Symmetry.Language
import Symmetry.Verify

m1 :: DSL repr => repr Int -> repr (Int :+: ())  
m1 = inl

m2 :: DSL repr => repr (Int :+: ())  
m2 = inr tt

mainProc :: forall repr.
            (DSL repr) => repr (Int -> ())
mainProc = lam $ \n -> exec $ do r <- newRMulti
                                 workers <- spawnMany r n worker
                                 let p = workers `lookup` int 0
                                 send p (m1 (int 0))
                                 doMany "l0" workers (lam $ \p -> send p m2)
                                 return tt
  where
    workerLoop = lam $ \f -> lam $ \_ -> do m <- recv
                                            match (m :: repr (Int :+: ()))
                                              (lam $ \_ -> app f tt)
                                              (lam $ \_ -> return tt)
    worker = app (fixM workerLoop) tt
                                 

main :: IO ()
main = checkerMain (int 3 |> mainProc)
