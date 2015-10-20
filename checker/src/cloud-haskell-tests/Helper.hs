{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}

module Helper where

import Data.Binary
import GHC.Generics (Generic)
import System.Random
import Control.Distributed.Process
import System.Directory
import Data.Typeable.Internal

any_bool :: Process Bool
any_bool  = liftIO $ do n <- randomIO :: IO Int
                        return (if n `mod` 2 == 1 then True else False)

any_nat :: Process PeanoN
any_nat  = getRandPInRange 1 5

getRandInRange    :: Int -> Int -> Process Int
getRandInRange b e = liftIO $ do n <- randomIO
                                 return ((n `mod` (e-b)) + b)

getRandLInRange      :: Int -> Int -> Int -> Process [Int]
getRandLInRange b e n = if n == 0
                           then return []
                           else do x <- getRandInRange b e
                                   l <- getRandLInRange b e (n-1)
                                   return (x:l)

data PeanoN = Zero | Succ PeanoN
             deriving (Ord, Eq, Read, Typeable, Generic)
instance Binary PeanoN

instance Show PeanoN where
  show p = show (fromPeano p)

toPeano n = if n == 0
            then Zero
            else Succ (toPeano (n-1))
fromPeano hn = case hn of
                 Zero   -> (0 :: Int)
                 Succ n -> 1 + (fromPeano n)

getRandPInRange b e    = getRandInRange b e >>= return . toPeano
getRandPLInRange b e n = do l <- getRandLInRange b e n
                            return (map toPeano l)
