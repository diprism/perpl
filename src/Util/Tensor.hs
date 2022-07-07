{- Tensor code for FGG factor generation -}

module Util.Tensor where
import Util.Helpers

-- Prelude's `zip` doesn't throw an error when the lists
-- have different lengths, dropping from the longer list
zipUnsafe :: [a] -> [b] -> [(a, b)]
zipUnsafe [] [] = []
zipUnsafe (a : as) (b : bs) = (a, b) : zipUnsafe as bs
zipUnsafe _ _ = error "zipping lists of different lengths"

-- Tensor can either be a Scalar or a Vector of more Tensors
data Tensor a = Scalar a | Vector [Tensor a]

-- Tensor instances:
instance Show a => Show (Tensor a) where
  show (Scalar a) = show a
  show (Vector ts) = '[' : delimitWith ", " [show v | v <- ts] ++ "]"

instance Functor Tensor where
  fmap f (Scalar a) = Scalar (f a)
  fmap f (Vector ts) = Vector [fmap f v | v <- ts]

instance Applicative Tensor where
  pure = Scalar
  Scalar f <*> Scalar a = Scalar (f a)
  Scalar f <*> Vector ta = Vector [Scalar f <*> v | v <- ta]
  Vector tf <*> Vector ta = Vector [vf <*> va | (vf, va) <- zipUnsafe tf ta]
  Vector tf <*> Scalar a = Vector [vf <*> Scalar a | vf <- tf]

instance Monad Tensor where
  Scalar a >>= f = f a
  Vector ta >>= f = Vector [va >>= f | va <- ta]


tensorJoin :: Tensor (Tensor a) -> Tensor a
tensorJoin (Scalar a) = a
tensorJoin (Vector ts) = Vector [tensorJoin v | v <- ts]

-- Squeezes all dimensions of size 1
squeeze :: Tensor a -> Tensor a
squeeze (Scalar a) = Scalar a
squeeze (Vector [t]) = squeeze t
squeeze (Vector ts) = Vector [squeeze v | v <- ts]

-- Inserts a size-1 dimension at index i
unsqueeze :: Int -> Tensor a -> Tensor a
unsqueeze 0 t = Vector [t]
unsqueeze i (Scalar a) = error "unsqueeze index out of range"
unsqueeze i (Vector ts) = Vector [unsqueeze (pred i) v | v <- ts]

-- Shape: (A1 × ... × An) -> (B1 × ... × Bm) -> (A1 × ... × An × B1 × ... × Bm)
tensorKron :: Tensor a -> Tensor b -> Tensor (a, b)
tensorKron ta tb = tensorJoin ((\ a -> (,) a <$> tb) <$> ta)

tensorKronAll :: [Tensor a] -> Tensor [a]
tensorKronAll = foldr (\ va t -> tensorJoin ((\ a -> (:) a <$> t) <$> va)) (Scalar [])

-- Zips two tensors together
tensorZip :: Tensor a -> Tensor b -> Tensor (a, b)
tensorZip ta tb = pure (,) <*> ta <*> tb

tensorShape :: Tensor a -> [Int]
tensorShape (Scalar a) = []
tensorShape (Vector []) = [0]
tensorShape (Vector ts) = length ts : tensorShape (head ts)

tensorAdd :: Num a => Tensor a -> Tensor a -> Tensor a
tensorAdd ta tb =
  pure (+) <*> ta <*> tb

vector :: [a] -> Tensor a
vector = Vector . map Scalar
matrix :: [[a]] -> Tensor a
matrix = Vector . map vector

-- Normally, we think of numbers with each digit in base 10:
--   "485" = 4*10² + 8*10¹ + 5*10⁰ = 485
-- However, this function allows us to compute the value of a variable-base number,
-- where each element in the input list is the pair (digit, base) s.t. 0 <= digit < base.
-- For example, consider if we wanted the 3 digits to have bases 6, 13, and 7:
--   "485" = 4*(13*7) + 8*(7) + 5*(1) = 425
-- We can compute this with toIdx [(4, 6), (8, 13), (5, 7)] (i.e. zip [4,8,5] [6,13,7])
-- This is useful for determining the actual index of something if you were to flatten
-- an n-dimensional tensor.
toIdx :: [(Int, Int)] -> Int
toIdx = fst . foldr (\ (i, l) (pi, pl) -> (i * pl + pi, l * pl)) (0, 1)

--           x[n]             x[m:n] or x[m:] or x[:n] or x[:]
data Slice = SliceIndex Int | SliceRange (Maybe Int) (Maybe Int)

tensorIndexError = error "misshaped tensor index"

-- Like (!!), but for n-dimensional tensors instead of lists
infixl 9 !!!
(!!!) :: Tensor a -> [Slice] -> Tensor a
ta !!! [] = ta
Scalar a !!! (SliceIndex i : ss) = tensorIndexError
Scalar a !!! (SliceRange s e : ss) = tensorIndexError
Vector a !!! (SliceIndex i : ss) = a !! i !!! ss
Vector a !!! (SliceRange s e : ss) =
  let s' = maybe 0 id s
      a' = maybe id (\ e' -> take (e' - s')) e (drop s' a)
  in
    Vector [v !!! ss | v <- a']

-- Returns the ith-row of an l×l identity matrix
tensorIdRow :: Num n => Int -> Int -> [n]
tensorIdRow i l = replicate i 0 ++ [1] ++ replicate (l - i - 1) 0

-- For [d1, d2, ..., dn], returns a 1-diagonal tensor
-- with shape [d1, d2, .., dn, (d1*d2*...*dn)]
tensorId :: Num n => [Int] -> Tensor n
tensorId dims =
  foldr
    (\ dim rt pos size -> Vector [rt (i + pos * dim) (size * dim) | i <- [0..dim-1]])
    (\ pos size -> Vector [Scalar n | n <- tensorIdRow pos size])
    dims 0 1

-- Fills a tensor with a value
constantTensor :: Num n => n -> [Int] -> Tensor n
constantTensor = foldr (\ dim t -> Vector (replicate dim t)) . Scalar

-- Tensor filled with zeros
zeros :: Num n => [Int] -> Tensor n
zeros = constantTensor 0

-- Tensor filled with ones
ones :: Num n => [Int] -> Tensor n
ones = constantTensor 1
