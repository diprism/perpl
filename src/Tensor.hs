module Tensor where
import Util

zipUnsafe :: [a] -> [b] -> [(a, b)]
zipUnsafe [] [] = []
zipUnsafe (a : as) (b : bs) = (a, b) : zipUnsafe as bs
zipUnsafe _ _ = error "zipping lists of different lengths"

data Tensor a = Scalar a | Vector [Tensor a]

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

squeeze :: Tensor a -> Tensor a
squeeze (Scalar a) = Scalar a
squeeze (Vector [t]) = squeeze t
squeeze (Vector ts) = Vector [squeeze v | v <- ts]

unsqueeze :: Int -> Tensor a -> Tensor a
unsqueeze 0 t = Vector [t]
unsqueeze i (Scalar a) = error "unsqueeze index out of range"
unsqueeze i (Vector ts) = Vector [unsqueeze (pred i) v | v <- ts]

tensorKron :: Tensor a -> Tensor b -> Tensor (a, b)
tensorKron ta tb = tensorJoin ((\ a -> (,) a <$> tb) <$> ta)

tensorKronAll :: [Tensor a] -> Tensor [a]
tensorKronAll = foldr (\ va t -> tensorJoin ((\ a -> (:) a <$> t) <$> va)) (Scalar [])

tensorZip :: Tensor a -> Tensor b -> Tensor (a, b)
tensorZip ta tb = pure (,) <*> ta <*> tb

tensorShape :: Tensor a -> [Int]
tensorShape (Scalar a) = []
tensorShape (Vector []) = [0]
tensorShape (Vector ts) = length ts : tensorShape (head ts)

vector :: [a] -> Tensor a
vector = Vector . map Scalar
matrix :: [[a]] -> Tensor a
matrix = Vector . map vector

toIdx :: [(Int, Int)] -> Int
toIdx = fst . foldr (\ (i, l) (pi, pl) -> (i * pl + pi, l * pl)) (0, 1)

data Slice = SliceIndex Int | SliceRange (Maybe Int) (Maybe Int)

tensorIndexError = error "misshaped tensor index"

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

tensorIdRow :: Num n => Int -> Int -> [n]
tensorIdRow i l = replicate i 0 ++ [1] ++ replicate (l - i - 1) 0

tensorId :: Num n => [Int] -> Tensor n
tensorId dims =
  foldr
    (\ dim rt pos size -> Vector [rt (i + pos * dim) (size * dim) | i <- [0..dim-1]])
    (\ pos size -> Vector [Scalar n | n <- tensorIdRow pos size])
    dims 0 1

constantTensor :: Num n => n -> [Int] -> Tensor n
constantTensor = foldr (\ dim t -> Vector (replicate dim t)) . Scalar

zeros :: Num n => [Int] -> Tensor n
zeros = constantTensor 0

ones :: Num n => [Int] -> Tensor n
ones = constantTensor 1
