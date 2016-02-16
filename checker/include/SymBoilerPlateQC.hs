{-# LANGUAGE OverloadedStrings #-}
module SymBoilerPlate where

import SymMap
import Control.Monad
import Data.Aeson
import Data.HashMap.Strict as H

{-@ nonDet :: a -> {v:Int | true} @-}
nonDet :: a -> Int
nonDet = undefined

{-@ nonDetRange :: x:Int -> y:Int -> {v:Int | x <= v && v < y} @-}  
nonDetRange :: Int -> Int -> Int
nonDetRange = undefined

instance DefaultMap Int where
  def = 0

instance DefaultMap (Val p) where
  def = VUnInit

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

instance (Show a) => Show (Val a) where
  show VUnit       = "VUnit"
  show VUnInit     = "VUnInit"
  show (VInt i)    = "VInt " ++ (show i)
  show (VString s) = "VString " ++ s
  show (VPid p)    = "VPid " ++ (show p)
  show (VInR v)    = "VInR " ++ (show v)
  show (VInL v)    = "VInL " ++ (show v)
  show (VPair l r) = "VPair (" ++ show l ++ ", " ++ show r ++ ")"

instance (FromJSON p) => FromJSON (Val p) where
  parseJSON (Object o) = case H.toList o of
    [(key,val)]
      | key == "VUnit"   -> return VUnit
      | key == "VUnInit" -> return VUnInit
      | key == "VInt"    -> VInt    <$> parseJSON val
      | key == "VString" -> VString <$> parseJSON val
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
  toJSON (VPid p)    = object [ "VPid"    .= toJSON p     ]
  toJSON (VInR v)    = object [ "VInR"    .= toJSON v     ]
  toJSON (VInL v)    = object [ "VInL"    .= toJSON v     ]
  toJSON (VPair l r) = object [ "VPair"   .= toJSON (l,r) ]

liquidAssert p x = if p
                     then x
                     else error "ASSERTION FAILURE !"

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
