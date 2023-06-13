module Util.Indices where

import Util.Tensor (Tensor(Scalar))
import Struct.Exprs (Ctor(Ctor), Type)

type PhysicalAxis = Int
data Axis =
    PhysicalAxis PhysicalAxis
  | ProductAxis [Axis]
  | SumAxis Int Axis Int

instance Show Axis where
  show (PhysicalAxis k) = show k
  show (ProductAxis es) = show es
  show (SumAxis before e after) = "{\"before\": " ++ show before
                              ++ ", \"term\": "   ++ show e
                              ++ ", \"after\": "  ++ show after
                              ++ "}"

data PatternedTensor a =
    PatternedTensor
      { physical :: Tensor a -- a physical tensor with n axes
      , expand   :: [Int]    -- a list with m counts
      , vaxes    :: [Axis] } -- a list in which each PhysicalAxis lies in [0,m+n)

instance Show a => Show (PatternedTensor a) where
  show pt = "{\"physical\": " ++ show (physical pt)
        ++ ", \"expand\": "   ++ show (expand pt)
        ++ ", \"vaxes\": "    ++ show (vaxes pt)
        ++ "}"

tensorId :: Num n => [Int] -> PatternedTensor n
tensorId dims = PatternedTensor (Scalar 1) dims (axes ++ [axis])
  where axes = zipWith (const PhysicalAxis) dims [0..]
        axis = ProductAxis axes

getCtorWeights :: Num n => (Type -> Int) -> Ctor -> [Ctor] -> PatternedTensor n
getCtorWeights size (Ctor x as) cs = PatternedTensor (Scalar 1) dims (axes ++ [axis])
  where dims = map size as
        axes = zipWith (const PhysicalAxis) dims [0..]
        (before, _:after) = break (\(Ctor x' as') -> x' == x) cs
        csize (Ctor x' as') | x' /= x = product (map size as')
        axis = SumAxis (sum (map csize before))
                       (ProductAxis axes)
                       (sum (map csize after))

getSumWeights :: Num n => [Int] -> Int -> PatternedTensor n
getSumWeights tpsizes k = PatternedTensor (Scalar 1) [m] [PhysicalAxis 0, axis]
  where (before, m:after) = splitAt k tpsizes
        axis = SumAxis (sum before)
                       (PhysicalAxis 0)
                       (sum after)
