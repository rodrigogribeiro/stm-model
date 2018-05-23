{-# LANGUAGE FlexibleInstances #-}
import Test.Tasty
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck


import STM.Basic.Definitions
import STM.Safety.Opacity
import STM.Semantics.TL2Semantics
import STM.Semantics.STMHaskellSemantics
import STM.Syntax.Syntax


interval :: (Int,Int)
interval = (1,5)

tests :: TestTree
tests = testGroup "Test suite"
           [
             QC.testProperty "Opacity for TL2 semantics" $ definitionOpacity tl2Semantics
           , QC.testProperty "Opacity for STM Haskell semantics" $ definitionOpacity stmHaskellSemantics
           ]

instance Arbitrary Var where
  arbitrary = Var <$> (suchThat arbitrary (>=0))

instance Arbitrary Val where
  arbitrary = Val <$> (suchThat arbitrary (>=0))

instance Arbitrary Tran where
  arbitrary = choose interval >>= genTran
  shrink = shrinkTran

newtype Program = Program {unProg :: [Proc]}
                  deriving (Eq, Ord, Show)

instance Arbitrary Program where
  arbitrary
    = do
        n <- choose (1,2)
        ps <- listOf (arbitrary :: Gen Proc)
        return (Program (take n ps))
        
genTran :: Int -> Gen Tran
genTran n
  | n <= 0 = TVal <$> arbitrary
  | otherwise
      = frequency
       [
         (1, TVal <$> arbitrary)
       , (n, TRead <$> arbitrary)
       , (n, TWrite <$> arbitrary <*> genTran (n - 1))
       , (n2, TOrElse <$> genTran n2 <*> genTran n2)  
       , (1, return TRetry)   
       , (n3, TIf <$> genTran n3 <*> genTran n3 <*> genTran n3)  
       , (n2, (:+:) <$> genTran n2 <*> genTran n2)
       ]
     where
       n2 = n `div` 2
       n3 = n `div` 3

shrinkTran :: Tran -> [Tran]
shrinkTran (TWrite v t) = [ TWrite v t' | t' <- shrink t]
shrinkTran (t `TOrElse` t') = concatMap shrink [t, t']
shrinkTran (TIf t t' t'') = concatMap shrink [t, t', t'']
shrinkTran (t :+: t') = concatMap shrink [t, t']
shrinkTran (TRead v) = [TRead v]
shrinkTran _ = []

instance Arbitrary Proc where
  arbitrary
    = choose interval >>= genProc
  shrink = shrinkProc  

genProc :: Int -> Gen Proc
genProc n
   | n <= 0 = PVal <$> arbitrary
   | otherwise
       = frequency
           [
             (1, PVal <$> arbitrary)
           , (n, PFork <$> genProc (n - 1))
           , (n, PAtomic Nothing <$> arbitrary)
           , (n, (:++:) <$> genProc n2 <*> genProc n2)
           ]
     where
       n2 = n `div` 2

shrinkProc :: Proc -> [Proc]
shrinkProc (PFork p) = [PFork p' | p' <- shrink p]
shrinkProc (PAtomic m t) = [PAtomic m t' | t' <- shrink t]
shrinkProc (p :++: p') = [p,p']
shrinkProc _ = []


main :: IO ()
main = defaultMain tests

-- Defining opacity

type Semantics = [Proc] -> Trace

definitionOpacity :: Semantics -> Program -> Bool
definitionOpacity sem
  = opacity . sem . unProg 

var :: Var
var = Var 0

t1 :: Tran
t1 = TRead var :+: TRead var :+: TRead var

t2 :: Tran
t2 = TWrite var (TVal (Val 1))

p :: Proc
p = PFork (PAtomic Nothing t1) :++: PFork (PAtomic Nothing t2)

--definitionMarkability :: Semantics -> Program -> Bool
--definitionMarkability sem
--  = markability . sem . unProg  
