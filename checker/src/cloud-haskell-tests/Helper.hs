{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

module Helper where

import Data.Binary
import Data.Typeable
import Data.Generics
import System.Random
import Control.Distributed.Process

matchMsgId1 mid p = matchIf (\ (m,_)     -> m == mid) (\(_,a)     -> p a)
matchMsgId2 mid p = matchIf (\ (m,_,_)   -> m == mid) (\(_,a,b)   -> p a b)
matchMsgId3 mid p = matchIf (\ (m,_,_,_) -> m == mid) (\(_,a,b,c) -> p a b c)
matchMsg    msg p = matchIf ((==) msg) (const p)

sendSuccess pid = send pid "ok"
waitForSuccess = receiveWait [matchIf ((==) "ok") doNothing]
                 where doNothing _ = return ()

class    MyFst a b | a -> b     where myfst :: a -> b
instance MyFst (a1,a2) a1       where myfst (x,_) = x
instance MyFst (a1,a2,a3) a1    where myfst (x,_,_) = x
instance MyFst (a1,a2,a3,a4) a1 where myfst (x,_,_,_) = x

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
             deriving (Ord, Eq, Read, Show, Typeable, Data)

toPeano n = if n == 0
            then Zero
            else Succ (toPeano (n-1))
fromPeano hn = case hn of
                 Zero   -> (0 :: Int)
                 Succ n -> 1 + (fromPeano n)

instance Binary PeanoN where
  put = put . fromPeano
  get = do i <- get :: Get Int
           return $ toPeano i

getRandPInRange b e    = getRandInRange b e >>= return . toPeano
getRandPLInRange b e n = do l <- getRandLInRange b e n
                            return (map toPeano l)
