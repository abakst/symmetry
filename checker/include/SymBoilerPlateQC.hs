{-# LANGUAGE OverloadedStrings #-}
module SymBoilerPlate where

import SymMap
import Control.Monad
import Data.Aeson
import Data.HashMap.Strict as H

import System.IO.Unsafe
import System.Random

{-@ nonDet :: a -> x:Int -> {v:Int | 0 <= v && v < x } @-}
nonDet :: a -> Int -> Int
nonDet _ x = nonDetRange 0 x 

{-@ nonDetRange :: x:Int -> y:Int -> {v:Int | x <= v && v < y} @-}  
nonDetRange :: Int -> Int -> Int
nonDetRange x y = unsafePerformIO $ do g      <- getStdGen
                                       (x, _) <- return $ randomR (x, y-1) g
                                       return x
                                        

instance DefaultMap Int where
  def = 0

instance DefaultMap (Val p) where
  def = VUnInit

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

instance (FromJSON p) => FromJSON (Val p) where
  parseJSON (Object o) = case H.toList o of
    [(key,val)]
      | key == "VUnit"   -> return VUnit
      | key == "VUnInit" -> return VUnInit
      | key == "VInt"    -> VInt    <$> parseJSON val
      | key == "VString" -> VString <$> parseJSON val
      | key == "VSet"    -> VSet    <$> parseJSON val
      | key == "VPid"    -> VPid    <$> parseJSON val
      | key == "VInR"    -> VInR    <$> parseJSON val
      | key == "VInL"    -> VInL    <$> parseJSON val
      | key == "VPair"   -> do (l,r) <- parseJSON val
                               return (VPair l r)
      | otherwise        -> mzero

  parseJSON _ = mzero

instance (ToJSON p) => ToJSON (Val p) where
  toJSON VUnit       = object [ "VUnit"   .= Null         ]
  toJSON VUnInit     = object [ "VUnInit" .= Null         ]
  toJSON (VInt i)    = object [ "VInt"    .= toJSON i     ]
  toJSON (VString s) = object [ "VString" .= toJSON s     ]
  toJSON (VSet s)    = object [ "VSet"    .= toJSON s     ]
  toJSON (VPid p)    = object [ "VPid"    .= toJSON p     ]
  toJSON (VInR v)    = object [ "VInR"    .= toJSON v     ]
  toJSON (VInL v)    = object [ "VInL"    .= toJSON v     ]
  toJSON (VPair l r) = object [ "VPair"   .= toJSON (l,r) ]

liquidAssert p x = if p
                     then Right x
                     else Left x

isVUnit, isVUnInit, isVInt, isVString, isVPid, isVInR, isVInL, isVPair, isVSet :: Val p -> Bool
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
