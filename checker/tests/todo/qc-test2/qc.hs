{-# LANGUAGE ScopedTypeVariables, FlexibleInstances #-}

module Qc () where

import SymVerify
import SymVector
import SymMap
import Language.Haskell.Liquid.Prelude

import Test.QuickCheck

main :: IO ()
main =  do quickCheck (\s plist -> runState s (getList plist) == ())

instance (Ord a, Arbitrary a, Arbitrary b) => Arbitrary (Map_t a b) where
  arbitrary = do k <- arbitrary
                 v <- arbitrary
                 return $ put empty k v

instance (Arbitrary a) => Arbitrary (Vec a) where
  arbitrary = do a <- arbitrary
                 return $ mkVec a

instance (Arbitrary a) => Arbitrary (Vec2D a) where
  arbitrary = do (x,y,a) <- arbitrary
                 return $ setVec2D x y a emptyVec2D

instance Arbitrary Val where
  arbitrary = oneof [ return VUnit
                    , VInt  <$> arbitrary
                    , VStr  <$> arbitrary
                    , VPid  <$> arbitrary
                    , VInL  <$> arbitrary
                    , VInR  <$> arbitrary
                    , VPair <$> arbitrary <*> arbitrary ]

role_1     = 2 :: Int
role_1_gen = suchThat arbitrary (\n -> 0 <= n && n < role_1)

instance (Arbitrary State) where
  arbitrary = State <$> return role_1 -- role_1            :: Int,
                    <*> role_1_gen    -- vP_role_1_k       :: Int,
                    <*> arbitrary     -- x_4               :: Map_t Int Val,
                    <*> arbitrary     -- x_5               :: Int,
                    <*> zero_n_map    -- vP_role_1_PCK     :: Map_t Int Int,
                    <*> zero_n_map    -- vP_role_1_RdK     :: Map_t Int Int,
                    <*> zero_n_map    -- vP_role_1_WrK     :: Map_t Int Int,
                    <*> return 0      -- PtrR_vP_0_0       :: Int,
                    <*> return 0      -- PtrW_vP_0_0       :: Int,
                    <*> arbitrary     -- vP_0_Buf_0        :: Vec Val,
                    <*> zero_map      -- PtrR_vP_role_1_0  :: Map_t Int Int,
                    <*> zero_map      -- PtrW_vP_role_1_0  :: Map_t Int Int,
                    <*> arbitrary     -- vP_role_1_Buf_0   :: Vec2D Val,
                    <*> return 0      -- vP_0_PC           :: Int,
                    <*> zero_map      -- vP_role_1_PC      :: Map_t Int Int
              where zero_map   = return $ foldr (\pid m -> put m pid 0) empty [0..role_1-1]
                    zero_n_map = return $ put empty 0 role_1

--instance (Arbitrary a) => (Arbitrary (PID_pre a)) where
instance Arbitrary (PID_pre Int) where
  arbitrary = oneof [return PID_vP_0, PID_vP_role_1 <$> role_1_gen  ]

data MyPidList = MyPidList {getList :: [PID_pre Int]}
                 deriving (Show)

minPidListLen = 2

instance Arbitrary MyPidList where
  arbitrary = MyPidList <$> suchThat arbitrary (\l -> length l > minPidListLen)
