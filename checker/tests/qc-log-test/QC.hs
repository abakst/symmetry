{-# Language RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
module QC () where
import SymVector
import SymMap
import SymVerify
import SymBoilerPlate
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Data.Aeson
import Data.Aeson.Encode.Pretty
import Control.Monad
import Data.ByteString.Lazy.Char8 as C (putStrLn)

main :: IO ()
main = quickCheck prop_runState

prop_runState :: State -> [Pid_pre] -> Property
prop_runState s plist = monadicIO $ do
  let l = runState s emptyVec emptyVec plist []
  if null l
     then return ()
     else run (log_states l)
  assert True

log_states   :: [State] -> IO ()
log_states l =  forM_ l (C.putStrLn . encodePretty . toJSON)

instance (Arbitrary a) => Arbitrary (Val a) where
  arbitrary = oneof [ return VUnit 
                    , return VUnInit 
                    , VInt    <$> arbitrary 
                    , VString <$> arbitrary 
                    , VPid    <$> arbitrary 
                    , VInL    <$> arbitrary 
                    , VInR    <$> arbitrary 
                    , VPair   <$> arbitrary <*> arbitrary ]

instance (Arbitrary a) => Arbitrary (Vec a) where 
   arbitrary = do a <- arbitrary 
                  return $ mkVec a

instance Arbitrary Pid_pre where
        arbitrary = elements [PIDR0, PIDR1]

instance Arbitrary State where
        arbitrary
          = State <$> return 0 <*> return 0 <*> return 0 <*> return 0 <*>
              return 0
              <*> return 0
              <*> arbitrary


-- data State = State{pidR0Pc :: Int, pidR1Pc :: Int,
--                    pidR0PtrR0 :: Int, pidR1PtrR0 :: Int, pidR0PtrW0 :: Int,
--                    pidR1PtrW0 :: Int, x_3 :: Val Pid_pre}
--            deriving Show

instance FromJSON State where
  parseJSON (Object s) = State <$>
                         s .: "pidR0Pc" <*>
                         s .: "pidR1Pc" <*>
                         s .: "pidR0PtrR0" <*>
                         s .: "pidR1PtrR0" <*>
                         s .: "pidR0PtrW0" <*>
                         s .: "pidR1PtrW0" <*>
                         s .: "x_3"
  parseJSON _            = mzero

instance ToJSON State where
  toJSON s@State{..} = object [ "pidR0Pc"    .= pidR0Pc
                              , "pidR1Pc"    .= pidR1Pc
                              , "pidR0PtrR0" .= pidR0PtrR0
                              , "pidR1PtrR0" .= pidR1PtrR0
                              , "pidR0PtrW0" .= pidR0PtrW0
                              , "pidR1PtrW0" .= pidR1PtrW0
                              , "x_3"        .= x_3        ]

-- data Pid_pre = PIDR0
--              | PIDR1
--              deriving Show

instance FromJSON Pid_pre where
  parseJSON (String s)
    | s == "PIDR0" = return PIDR0
    | s == "PIDR1" = return PIDR1
  parseJSON _ = mzero

instance ToJSON Pid_pre where
  toJSON PIDR0 = String "PIDR0"
  toJSON PIDR1 = String "PIDR1"

-- data Pid_pre p1 = PIDR0
--                 | PIDR2 p1
--                 deriving Show

instance FromJSON p1 => FromJSON (Pid_pre p1) where
        parseJSON (Object s)
          = case H.toList s of
              [(key,value)] | key == "PIDR0" -> return PIDR0
                            | key == "PIDR2" -> PIDR2 <$> parseJSON value
        parseJSON _ = mzero
