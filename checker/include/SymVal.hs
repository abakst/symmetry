module SymBoiler where

{-@ nonDet :: a -> {v:Int | true} @-}
nonDet :: a -> Int
nonDet = undefined

{-@
 data Val p = VUnit {}
           | VUnInit {}
           | VInt { vInt :: Int }
           | VString { vString :: String }
           | VPid { vPid :: p }
           | VInR { vInR :: Val p }
           | VInL { vInL :: Val p }
           | VPair { vLeft :: Val p, vRight :: Val p }
@-}
data Val p = VUnit {}
           | VUnInit {}
           | VInt { vInt :: Int }
           | VString { vString :: String }
           | VPid { vPid :: p }
           | VInR { vInR :: Val p }
           | VInL { vInL :: Val p }
           | VPair { vLeft :: Val p, vRight :: Val p }
           deriving Show

isVUnit, isVUnInit, isVInt, isVString, isVPid, isVInR, isVInL, isVPair :: Val p -> Bool
isVUnit VUnit{} = True
isVUnit _       = False

isVUnInit VUnInit{} = True
isVUnInit _         = False

isVInt VInt{} = True
isVInt _      = False

isVString VString{} = True
isVString _         = False

isVPid VPid{} = True
isVPid _         = False

isVInR VInR{} = True
isVInR _         = False

isVInL VInL{} = True
isVInL _         = False

isVPair VPair{} = True
isVPair _         = False

{-@ measure isVUnit   @-}
{-@ measure isVUnInit @-}
{-@ measure isVInt    @-}
{-@ measure isVString @-}
{-@ measure isVPid    @-}
{-@ measure isVInL    @-}
{-@ measure isVInR    @-}
{-@ measure isVPair   @-}
