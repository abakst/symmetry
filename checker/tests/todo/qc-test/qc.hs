module Qc where

import SymVerify
import SymVector
import SymMap

import Test.QuickCheck

main :: IO ()
main =  do quickCheck (\s plist -> runState s (getList plist) == ())

instance (Arbitrary a) => Arbitrary (Vec a) where
  arbitrary = do a <- arbitrary
                 return $ mkVec a

instance Arbitrary Val where
  arbitrary = oneof [ return VUnit
                    , VInt <$> arbitrary
                    , VStr <$> arbitrary
                    , VPid <$> arbitrary
                    , VInL <$> arbitrary
                    , VInR <$> arbitrary
                    , VPair <$> arbitrary <*> arbitrary ]

instance (Arbitrary State) where
  arbitrary = State <$> arbitrary
                    <*> arbitrary
                    <*> arbitrary
                    <*> arbitrary
                    <*> arbitrary
                    <*> arbitrary
                    <*> arbitrary
                    <*> arbitrary
                    <*> arbitrary

instance (Arbitrary PID_pre) where
  arbitrary = elements [PID_vP_0, PID_vP_1]

data MyPidList = MyPidList {getList :: [PID_pre]}
                 deriving (Show)

minPidListLen = 10

instance Arbitrary MyPidList where
  arbitrary = MyPidList <$> suchThat arbitrary (\l -> length l > minPidListLen)
