module SymBoilerPlate where

{-@ nonDet :: a -> x:Int -> {v:Int | 0 <= v && v < x } @-}
nonDet :: a -> Int -> Int
nonDet = undefined

{-@ nonDetRange :: x:Int -> y:Int -> {v:Int | x <= v && v < y} @-}  
nonDetRange :: Int -> Int -> Int
nonDetRange = undefined

{-@
 data Val p = VUnit {}
           | VUnInit {}
           | VInt { vInt :: Int }
           | VString { vString :: String }
           | VSet { vSetName :: String }
           | VPid { vPid :: p }
           | VInR { vInR :: Val p }
           | VInL { vInL :: Val p }
           | VPair { vLeft :: Val p, vRight :: Val p }
@-}
data Val p = VUnit {}
             | VUnInit {}
             | VInt { vInt :: Int }
             | VString { vString :: String }
             | VSet { vSetName :: String }
             | VPid { vPid :: p }
             | VInR { vInR :: Val p }
             | VInL { vInL :: Val p }
             | VPair { vLeft :: Val p, vRight :: Val p }
             deriving (Show)

isVUnit, isVUnInit, isVInt, isVString, isVPid, isVInR, isVInL, isVPair, isSet :: Val p -> Bool

isVUnit VUnit{} = True
isVUnit _       = False

isVUnInit VUnInit{} = True
isVUnInit _         = False

isVInt VInt{} = True
isVInt _      = False

isVString VString{} = True
isVString _         = False

isVSet VSet{} = True
isVSet _      = False
                

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
{-@ measure isVSet    @-}
