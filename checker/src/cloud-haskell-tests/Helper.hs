{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

module Helper where

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
