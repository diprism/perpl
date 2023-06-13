module Util.Indices (PatternedTensor(..)) where

import Util.Tensor (Tensor(Scalar), TensorLike(..))
import Util.JSON (JSON(JSint, JSarray, JSobject))
import Struct.Exprs (Ctor(Ctor))
import Struct.Show ()

type PhysicalAxis = Int
data Axis =
    PhysicalAxis PhysicalAxis
  | ProductAxis [Axis]
  | SumAxis Int Axis Int

axis_to_json :: Axis -> JSON
axis_to_json (PhysicalAxis k) = JSint k
axis_to_json (ProductAxis es) = JSarray (map axis_to_json es)
axis_to_json (SumAxis before e after) = JSobject [("before", JSint before),
                                                  ("term", axis_to_json e),
                                                  ("after", JSint after)]

axisNelem :: [Int] -> Axis -> Int
axisNelem env (PhysicalAxis k) = env !! k
axisNelem env (ProductAxis es) = product (map (axisNelem env) es)
axisNelem env (SumAxis before e after) = before + axisNelem env e + after

data PatternedTensor a =
    PatternedTensor
      { physical :: Tensor a -- a physical tensor with n axes
      , expand   :: [Int]    -- a list with m counts
      , vaxes    :: [Axis] } -- a list in which each PhysicalAxis lies in [0,m+n)

instance TensorLike PatternedTensor where
  weights_to_json pt = JSobject [("physical", weights_to_json (physical pt)),
                                 ("expand", JSarray (map JSint (expand pt))),
                                 ("vaxes", JSarray (map axis_to_json (vaxes pt)))]

  fromTensor t = PatternedTensor t [] axes
    where axes = zipWith (const PhysicalAxis) (tensorShape t) [0..]

  tensorShape pt = map (axisNelem (expand pt ++ tensorShape (physical pt)))
                       (vaxes pt)

  tensorId dims = PatternedTensor (Scalar 1) dims (axes ++ [axis])
    where axes = zipWith (const PhysicalAxis) dims [0..]
          axis = case axes of [e] -> e
                              _   -> ProductAxis axes

  tensorCtor size (Ctor x as) cs = PatternedTensor (Scalar 1) dims (axes ++ [axis])
    where dims = map size as
          axes = zipWith (const PhysicalAxis) dims [0..]
          (cbefore, _:cafter) = break (\(Ctor x' as') -> x' == x) cs
          csize (Ctor x' as') | x' /= x   = product (map size as')
                              | otherwise = error ("Duplicate constructor " ++ show x)
          before = sum (map csize cbefore)
          after  = sum (map csize cafter)
          axis | before == 0 && after == 0 = e
               | otherwise = SumAxis before (e) after
            where e = case axes of [e] -> e
                                   _   -> ProductAxis axes

  tensorSum tpsizes k = PatternedTensor (Scalar 1) [m] [PhysicalAxis 0, axis]
    where (mbefore, m:mafter) = splitAt k tpsizes
          before = sum mbefore
          after  = sum mafter
          axis | before == 0 && after == 0 = PhysicalAxis 0
               | otherwise = SumAxis before (PhysicalAxis 0) after
