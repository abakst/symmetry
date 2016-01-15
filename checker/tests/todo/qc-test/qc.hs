{-# LANGUAGE ScopedTypeVariables #-}

module Qc () where

import SymVerify
import SymVector
import SymMap
import Language.Haskell.Liquid.Prelude

import Test.QuickCheck

main :: IO ()
main =  do quickCheck (\s plist -> runState s (getList plist) == ())


instance (Arbitrary a) => Arbitrary (Vec a) where
  arbitrary = do a <- arbitrary
                 return $ mkVec a

instance Arbitrary Val where
  arbitrary = oneof [ return VUnit
                    , VInt  <$> arbitrary
                    , VStr  <$> arbitrary
                    , VPid  <$> arbitrary
                    , VInL  <$> arbitrary
                    , VInR  <$> arbitrary
                    , VPair <$> arbitrary <*> arbitrary ]

instance (Arbitrary State) where
  arbitrary = State <$> arbitrary -- x_3
                    <*> (return 0) -- PtrR_vP_0_0
                    <*> (return 0) -- PtrW_vP_0_0
                    <*> arbitrary -- vP_0_Buf_0
                    <*> (return 0) -- PtrR_vP_1_0
                    <*> (return 0) -- PtrW_vP_1_0
                    <*> arbitrary -- vP_1_Buf_0
                    <*> (return 0) -- vP_0_PC
                    <*> (return 0) -- vP_1_PC

instance (Arbitrary PID_pre) where
  arbitrary = elements [PID_vP_0, PID_vP_1]

data MyPidList = MyPidList {getList :: [PID_pre]}
                 deriving (Show)

minPidListLen = 2

instance Arbitrary MyPidList where
  arbitrary = MyPidList <$> suchThat arbitrary (\l -> length l > minPidListLen)
