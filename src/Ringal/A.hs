{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- <https://blog.jle.im/entry/functor-combinatorpedia.html>
-- <https://en.wikipedia.org/wiki/Monoidal_functor>
-- <https://en.wikipedia.org/wiki/Ring_(mathematics)>
-- <https://en.wikipedia.org/wiki/Semigroup>
-- <https://en.wikipedia.org/wiki/Tropical_semiring>
-- <https://lukajcb.github.io/blog/functional/2018/11/02/a-tale-of-semirings.html>
-- <https://stackoverflow.com/questions/50702929/monoidal-functor-is-applicative-but-where-is-the-monoid-typeclass-in-the-definit/50717675#50717675>
-- <https://typeclasses.com/semiring>

module Ringal.A where

import qualified Prelude
import Prelude hiding ( Applicative(..)
                      , Foldable(..)
                      , Functor(..)
                      , Monoid(..)
                      , Num(..)
                      , Semigroup(..)
                      , map)

import Data.Kind
import Data.These hiding (assoc, swap)
import qualified Data.Void
import Data.Void hiding (absurd)
import GHC.Natural



data Law a = Equal a a
  deriving (Eq, Ord, Read, Show)



class AdditiveSemigroup a where
  (+) :: a -> a -> a

prop_add_assoc :: AdditiveSemigroup a => a -> a -> a -> Law a
prop_add_assoc x y z = Equal ((x + y) + z) (x + (y + z))

class AdditiveSemigroup a => AdditiveCommutative a

prop_add_comm :: AdditiveSemigroup a => a -> a -> Law a
prop_add_comm x y = Equal (x + y) (y + x)

class AdditiveSemigroup a => AdditiveMonoid a where
  zero :: a

prop_add_idleft :: AdditiveMonoid a => a -> Law a
prop_add_idleft x = Equal x (zero + x)

prop_add_idright :: AdditiveMonoid a => a -> Law a
prop_add_idright x = Equal x (x + zero)

class AdditiveMonoid a => AdditiveGroup a where
  negate :: a -> a

prop_add_invleft :: AdditiveGroup a => a -> Law a
prop_add_invleft x = Equal zero (negate x + x)

prop_add_invright :: AdditiveGroup a => a -> Law a
prop_add_invright x = Equal zero (x + negate x)



class Semigroup a where
  (*) :: a -> a -> a

class Semigroup a => Commutative a

class Semigroup a => Monoid a where
  one :: a

class Monoid a => Group a where
  inverse :: a -> a



class (AdditiveMonoid a, AdditiveCommutative a, Monoid a) => Semiring a where
  fromInteger :: Integer -> a
  toInteger :: a -> Integer

prop_distleft :: Semiring a => a -> a -> a -> Law a
prop_distleft x y z = Equal (x * (y + z)) (x * y + x * z)

prop_distright :: Semiring a => a -> a -> a -> Law a
prop_distright x y z = Equal ((x + y) * z) (x * z + y * z)

prop_absleft :: Semiring a => a -> Law a
prop_absleft x = Equal zero (zero * x)

prop_absright :: Semiring a => a -> Law a
prop_absright x = Equal zero (x * zero)

class (Semiring a, AdditiveGroup a) => Ring a



data InfNatural = InfNat
                | FinNat { getFinNat :: Natural }
  deriving (Eq, Ord, Read, Show)

instance AdditiveSemigroup InfNatural where
  InfNat + _ = InfNat
  _ + InfNat = InfNat
  FinNat x + FinNat y = FinNat (x Prelude.+ y)
instance AdditiveCommutative InfNatural
instance AdditiveMonoid InfNatural where zero = FinNat 0
instance Semigroup InfNatural where
  InfNat * InfNat = InfNat
  FinNat x * FinNat y = FinNat (x Prelude.* y)
  InfNat * FinNat x = if x == 0 then undefined else InfNat
  x * y = y * x
instance Monoid InfNatural where one = FinNat 1
instance Semiring InfNatural where
  fromInteger = FinNat . Prelude.fromInteger
  toInteger = Prelude.toInteger . getFinNat

data InfInteger = PosInf
                | NegInf
                | Finite { getFinite :: Integer }
  deriving (Eq, Ord, Read, Show)

instance AdditiveSemigroup InfInteger where
  PosInf + NegInf = undefined
  PosInf + _ = PosInf
  NegInf + PosInf = undefined
  NegInf + _ = NegInf
  Finite _ + PosInf = PosInf
  Finite _ + NegInf = NegInf
  Finite x + Finite y = Finite (x Prelude.+ y)
instance AdditiveCommutative InfInteger
instance AdditiveMonoid InfInteger where zero = Finite 0
instance Semigroup InfInteger where
  PosInf * PosInf = PosInf
  PosInf * NegInf = NegInf
  PosInf * Finite x = case compare x 0 of EQ -> undefined
                                          GT -> PosInf
                                          LT -> NegInf
  NegInf * PosInf = NegInf
  NegInf * NegInf = PosInf
  NegInf * Finite x = case compare x 0 of EQ -> undefined
                                          GT -> NegInf
                                          LT -> PosInf
  Finite x * Finite y = Finite (x Prelude.* y)
  x * y = y * x
instance Monoid InfInteger where one = Finite 1
instance Semiring InfInteger where
  fromInteger = Finite . Prelude.fromInteger
  toInteger = Prelude.toInteger . getFinite



-- We have the following semirings:
--    (Natural | Integer, +, *, 0, 1)
--
--    (InfNatural | InfInteger | Double, min, +, inf, 0)
--    (InfInteger | Double, max, +, -inf, 0)
--
--    (Natural, max, +, 0, 0)
--
--    (Natural, max, *, 0, 1)

instance AdditiveSemigroup Int where (+) = (Prelude.+)
instance AdditiveCommutative Int
instance AdditiveMonoid Int where zero = 0
instance Semigroup Int where (*) = (Prelude.*)
instance Monoid Int where one = 1
instance Semiring Int where
  fromInteger = Prelude.fromInteger
  toInteger = Prelude.toInteger

newtype MinPlus a = MinPlus { getMinPlus :: a }
minplus1 :: (a -> b) -> MinPlus a -> MinPlus b
minplus1 f (MinPlus x) = MinPlus (f x)
minplus2 :: (a -> b -> c) -> MinPlus a -> MinPlus b -> MinPlus c
minplus2 f (MinPlus x) (MinPlus y) = MinPlus (f x y)

instance AdditiveSemigroup (MinPlus Int) where (+) = minplus2 Prelude.min
instance AdditiveCommutative (MinPlus Int)
instance AdditiveMonoid (MinPlus Int) where zero = MinPlus Prelude.maxBound
instance Semigroup (MinPlus Int) where (*) = minplus2 (Prelude.+)
instance Monoid (MinPlus Int) where one = MinPlus 0
instance Semiring (MinPlus Int) where
  fromInteger = MinPlus . Prelude.fromInteger
  toInteger = Prelude.toInteger . getMinPlus

instance AdditiveSemigroup (MinPlus Word) where (+) = minplus2 Prelude.min
instance AdditiveCommutative (MinPlus Word)
instance AdditiveMonoid (MinPlus Word) where zero = MinPlus Prelude.maxBound
instance Semigroup (MinPlus Word) where (*) = minplus2 (Prelude.+)
instance Monoid (MinPlus Word) where one = MinPlus 0
instance Semiring (MinPlus Word) where
  fromInteger = MinPlus . Prelude.fromInteger
  toInteger = Prelude.toInteger . getMinPlus

newtype MaxPlus a = MaxPlus { getMaxPlus :: a }
maxplus1 :: (a -> b) -> MaxPlus a -> MaxPlus b
maxplus1 f (MaxPlus x) = MaxPlus (f x)
maxplus2 :: (a -> b -> c) -> MaxPlus a -> MaxPlus b -> MaxPlus c
maxplus2 f (MaxPlus x) (MaxPlus y) = MaxPlus (f x y)

instance AdditiveSemigroup (MaxPlus Int) where (+) = maxplus2 Prelude.max
instance AdditiveCommutative (MaxPlus Int)
instance AdditiveMonoid (MaxPlus Int) where zero = MaxPlus Prelude.minBound
instance Semigroup (MaxPlus Int) where (*) = maxplus2 (Prelude.+)
instance Monoid (MaxPlus Int) where one = MaxPlus 0
instance Semiring (MaxPlus Int) where
  fromInteger = MaxPlus . Prelude.fromInteger
  toInteger = Prelude.toInteger . getMaxPlus

instance AdditiveSemigroup (MaxPlus Word) where (+) = maxplus2 Prelude.max
instance AdditiveCommutative (MaxPlus Word)
instance AdditiveMonoid (MaxPlus Word) where zero = MaxPlus Prelude.minBound
instance Semigroup (MaxPlus Word) where (*) = maxplus2 (Prelude.+)
instance Monoid (MaxPlus Word) where one = MaxPlus 0
-- ^ Not a semiring, does not absorb! Need infinity!
-- > instance Semiring (MaxPlus Word) where
-- >   fromInteger = MaxPlus . Prelude.fromInteger
-- >   toInteger = Prelude.toInteger . getMaxPlus

newtype MaxTimes a = MaxTimes { getMaxTimes :: a }
maxtimes1 :: (a -> b) -> MaxTimes a -> MaxTimes b
maxtimes1 f (MaxTimes x) = MaxTimes (f x)
maxtimes2 :: (a -> b -> c) -> MaxTimes a -> MaxTimes b -> MaxTimes c
maxtimes2 f (MaxTimes x) (MaxTimes y) = MaxTimes (f x y)

instance AdditiveSemigroup (MaxTimes Word) where (+) = maxtimes2 Prelude.max
instance AdditiveCommutative (MaxTimes Word)
instance AdditiveMonoid (MaxTimes Word) where zero = MaxTimes Prelude.minBound
instance Semigroup (MaxTimes Word) where (*) = maxtimes2 (Prelude.+)
instance Monoid (MaxTimes Word) where one = MaxTimes 1
instance Semiring (MaxTimes Word) where
  fromInteger = MaxTimes . Prelude.fromInteger
  toInteger = Prelude.toInteger . getMaxTimes
-- ^ Note that 'MinTimes Word' is not a 'Semiring'.



--------------------------------------------------------------------------------



class Functor f where
  map :: (a -> b) -> f a -> f b

class Functor f => Foldable f where
  length :: f a -> Int



instance Functor [] where map = Prelude.map
instance Foldable [] where length = Prelude.length



--------------------------------------------------------------------------------



class Bifunctor f where
  bimap :: (a -> c) -> (b -> d) -> f a b -> f c d

-- See package 'assoc-1'
class Bifunctor f => Biassociative f where
  biassoc :: f (f a b) c -> f a (f b c)
  bireassoc :: f a (f b c) -> f (f a b) c

law_biassoc :: Biassociative f => f (f a b) c -> Law (f (f a b) c)
law_biassoc xyzs = Equal xyzs (bireassoc (biassoc xyzs))

law_bireassoc :: Biassociative f => f a (f b c) -> Law (f a (f b c))
law_bireassoc xyzs = Equal xyzs (biassoc (bireassoc xyzs))

-- Package 'assoc-1' suggests:
-- prop> assoc . bimap (bimap f g) h = bimap f (bimap g h) . assoc

class Bifunctor f => Bicommutative f where
  biswap :: f a b -> f b a

law_biswap :: Bicommutative f => f a b -> Law (f a b)
law_biswap xys = Equal xys (biswap (biswap xys))

-- Make this 'Bimonoidal', and require 'Biassociative'?
class Bifunctor f => Biunital f u | f -> u where
  bilunit :: a -> f u a
  bilreunit :: f u a -> a
  birunit :: a -> f a u
  birreunit :: f a u -> a

law_bilunit :: forall f u a. Biunital f u => a -> Law a
law_bilunit x = Equal x (bilreunit (bilunit @f @u x))

law_bilreunit :: Biunital f u => f u a -> Law (f u a)
law_bilreunit xs = Equal xs (bilunit (bilreunit xs))

law_birunit :: forall f u a. Biunital f u => a -> Law a
law_birunit x = Equal x (birreunit (birunit @f @u x))

law_birreunit :: Biunital f u => f a u -> Law (f a u)
law_birreunit xs = Equal xs (birunit (birreunit xs))



instance Bifunctor (,) where
  bimap f g (x, y) = (f x, g y)
instance Biassociative (,) where
  biassoc ((x, y), z) = (x, (y, z))
  bireassoc (x, (y, z)) = ((x, y), z)
instance Bicommutative (,) where
  biswap (x, y) = (y, x)
instance Biunital (,) () where
  bilunit x = ((), x)
  bilreunit (_, x) = x
  birunit x = (x, ())
  birreunit (x, _) = x

instance Bifunctor Either where
  bimap f _ (Left x) = Left (f x)
  bimap _ g (Right y) = Right (g y)
instance Biassociative Either where
  biassoc (Left (Left x)) = Left x
  biassoc (Left (Right y)) = Right (Left y)
  biassoc (Right z) = Right (Right z)
  bireassoc (Left x) = Left (Left x)
  bireassoc (Right (Left y)) = Left (Right y)
  bireassoc (Right (Right z)) = Right z
instance Bicommutative Either where
  biswap (Left x) = Right x
  biswap (Right y) = Left y
instance Biunital Either Void where
  bilunit x = Right x
  bilreunit (Left _) = undefined
  bilreunit (Right x) = x
  birunit x = Left x
  birreunit (Left x) = x
  birreunit (Right _) = undefined

instance Bifunctor These where
  bimap f g (This x)    = This (f x)
  bimap f g (That y)    = That (g y)
  bimap f g (These x y) = These (f x) (g y)
instance Biassociative These where
  biassoc (This (This x))       = This x
  biassoc (This (That y))       = That (This y)
  biassoc (That z)              = That (That z)
  biassoc (These (That y) z)    = That (These y z)
  biassoc (This (These x y))    = These x (This y)
  biassoc (These (This x) z)    = These x (That z)
  biassoc (These (These x y) z) = These x (These y z)
  bireassoc (This x)              = This (This x)
  bireassoc (That (This y))       = This (That y)
  bireassoc (That (That z))       = That z
  bireassoc (That (These y z))    = These (That y) z
  bireassoc (These x (This y))    = This (These x y)
  bireassoc (These x (That z))    = These (This x) z
  bireassoc (These x (These y z)) = These (These x y) z
instance Bicommutative These where
  biswap (This x)    = That x
  biswap (That y)    = This y
  biswap (These x y) = These y x
instance Biunital These Void where
  bilunit x = That x
  bilreunit (This _) = undefined
  bilreunit (That x) = x
  bilreunit (These _ _) = undefined
  birunit x = This x
  birreunit (This x) = x
  birreunit (That _) = undefined
  birreunit (These _ _) = undefined



--------------------------------------------------------------------------------



-- newtype f ~> g = Nat (forall a. f a -> g a)
-- newtype f ~~> g = Binat (forall a b. f a b -> g a b)

data Sum f g a = InL (f a) | InR (g a)
  deriving (Eq, Ord, Read, Show)
data Product f g a = Product (f a) (g a)
  deriving (Eq, Ord, Read, Show)
data Empty a
newtype Unit a = Unit a
  deriving (Eq, Ord, Read, Show)

instance (Functor f, Functor g) => Functor (Sum f g) where
  map f (InL xs) = InL (map f xs)
  map f (InR ys) = InR (map f ys)
instance (Functor f, Functor g) => Functor (Product f g) where
  map f (Product xs ys) = Product (map f xs) (map f ys)
instance Functor Empty where
  map _ _ = undefined
instance Functor Unit where
  map f (Unit x) = Unit (f x)

instance (Foldable f, Foldable g) => Foldable (Sum f g) where
  length (InL xs) = length xs
  length (InR ys) = length ys
instance (Foldable f, Foldable g) => Foldable (Product f g) where
  length (Product xs ys) = length xs + length ys
instance Foldable Empty where
  length _ = 0
instance Foldable Unit where
  length _ = 1



--------------------------------------------------------------------------------



-- See also Tannen: (<+>) :: f -> f -> Tannen f s

class (Functor f, Biassociative s) => AdditiveSemigroupal f s | f -> s where
  -- (<+>) :: Product f f ~~> f
  -- (<+>) :: f a -> f b -> f (Either a b)
  (<+>) :: f a -> f b -> f (s a b)

prop_fadd_assoc :: AdditiveSemigroupal f s
                => f a -> f b -> f c -> Law (f (s a (s b c)))
prop_fadd_assoc xs ys zs =
  Equal (map biassoc ((xs <+> ys) <+> zs)) (xs <+> (ys <+> zs))

class (AdditiveSemigroupal f s, Bicommutative s) => AdditiveCommutatival f s

prop_fadd_comm :: AdditiveCommutatival f s => f a -> f b -> Law (f (s b a))
prop_fadd_comm xs ys = Equal (map biswap (xs <+> ys)) (ys <+> xs)

class (AdditiveSemigroupal f s, Biunital s z) =>
      AdditiveMonoidal f s z | f -> z where
  {-# MINIMAL absurd, (empty | empty') #-}
  -- empty :: f Void
  -- | Technically, this should be 'f Void', but since 'f' is a
  -- functor, we can always map a function 'Void -> a', which is
  -- 'absurd'.
  absurd :: z -> a
  empty :: f a
  empty = map (absurd @f . birreunit) empty'
  empty' :: f (s z z)
  empty' = empty

prop_fadd_idleft :: AdditiveMonoidal f s z => f a -> Law (f a)
prop_fadd_idleft xs = Equal (map bilreunit (empty <+> xs)) xs

prop_fadd_idright :: AdditiveMonoidal f s z => f a -> Law (f a)
prop_fadd_idright xs = Equal (map birreunit (xs <+> empty)) xs



class (Functor f, Biassociative p) => Semigroupal f p | f -> p where
  -- (<*>) :: Product f f ~~> f
  (<*>) :: f a -> f b -> f (p a b)

prop_fmul_assoc :: Semigroupal f p
                => f a -> f b -> f c -> Law (f (p a (p b c)))
prop_fmul_assoc xs ys zs =
  Equal (map biassoc ((xs <*> ys) <*> zs)) (xs <*> (ys <*> zs))

class (Semigroupal f p, Bicommutative p) => Commutatival f p

prop_fmul_comm :: Commutatival f p => f a -> f b -> Law (f (p b a))
prop_fmul_comm xs ys = Equal (map biswap (xs <*> ys)) (ys <*> xs)

class (Semigroupal f p, Biunital p u) => Monoidal f p u | f -> u where
  -- unit :: f ()
  -- | Technically, this should be 'f ()', but since 'f' is a functor,
  -- we can always map a function '() -> a', which is equivalent to a
  -- constant.
  it :: u
  unit :: a -> f a
  unit x = map (const x) unit'
  unit' :: f (p u u)
  unit' = unit (bilunit (it @f))

prop_fmul_idleft :: forall f p u a. Monoidal f p u => f a -> Law (f a)
prop_fmul_idleft xs = Equal (map bilreunit (unit (it @f) <*> xs)) xs

prop_fmul_idright :: forall f p u a. Monoidal f p u => f a -> Law (f a)
prop_fmul_idright xs = Equal (map birreunit (xs <*> unit (it @f))) xs



--------------------------------------------------------------------------------



instance AdditiveSemigroup [a] where (+) = (++)
instance AdditiveMonoid [a] where zero = []



newtype EitherList a = EitherList { getEitherList :: [a] }
  deriving (Eq, Ord, Read, Show)
  deriving (Foldable, Functor) via []

instance AdditiveSemigroupal EitherList Either where
  EitherList (x:xs) <+> ys = EitherList (Left x : rs)
    where EitherList rs = EitherList xs <+> ys
  EitherList [] <+> EitherList (y:ys) = EitherList (Right y : rs)
    where EitherList rs = EitherList [] <+> EitherList ys
  EitherList _ <+> EitherList _ = EitherList []

instance AdditiveCommutatival EitherList Either

instance AdditiveMonoidal EitherList Either Void where
  absurd = Data.Void.absurd
  empty = EitherList []



newtype TheseList a = TheseList { getTheseList :: [a] }
  deriving (Eq, Ord, Read, Show)
  deriving (Foldable, Functor) via []

instance AdditiveSemigroupal TheseList These where
  TheseList (x:xs) <+> TheseList (y:ys) = TheseList (These x y : rs)
    where TheseList rs = TheseList xs <+> TheseList ys
  TheseList (x:xs) <+> TheseList [] = TheseList (This x : rs)
    where TheseList rs = TheseList xs <+> TheseList []
  TheseList [] <+> TheseList (y:ys) = TheseList (That y : rs)
    where TheseList rs = TheseList [] <+> TheseList ys
  TheseList _ <+> TheseList _ = TheseList []

instance AdditiveCommutatival TheseList These

instance AdditiveMonoidal TheseList These Void where
  absurd = Data.Void.absurd
  empty = TheseList []



newtype ZipList a = ZipList { getZipList :: [a] }
  deriving (Eq, Ord, Read, Show)
  deriving (Foldable, Functor) via []

instance Semigroupal ZipList (,) where
  ZipList (x:xs) <*> ZipList (y:ys) = ZipList ((x,y) : rs)
    where ZipList rs = ZipList xs <*> ZipList ys
  ZipList _ <*> ZipList _ = ZipList []

instance Commutatival ZipList (,)

instance Monoidal ZipList (,) () where
  -- TODO: WHY IS THIS MULTIPLICATIVE? I WANT THIS TO BE ADDITIVE, OR HAVE A CHOICE
  -- USE FUNCTIONS INSTEAD OF BIFUNCTORS
  it = ()
  unit x = ZipList (repeat x)



instance Semigroupal [] (,) where
  xs <*> ys = [(x, y) | x <- xs, y <- ys]

instance Monoidal [] (,) () where
  it = ()
  unit x = [x]



-- > prop_length_zip :: (ZippyMonoidal f, Foldable f) => f a -> f b -> Law Int
-- > prop_length_zip xs ys = Equal (min (length xs) (length ys)) (length (xs <&> ys))

-- > prop_length_add :: (AdditiveMonoidal f, Foldable f) => f a -> f b -> Law Int
-- > prop_length_add xs ys = Equal (length xs + length ys) (length (xs <+> ys))

-- > prop_length_mul :: (Monoidal f, Foldable f) => f a -> f b -> Law Int
-- > prop_length_mul xs ys = Equal (length xs * length ys) (length (xs <*> ys))






-- Question: Do ('<|>', '<+>') and/or ('<+>', '<*>') form a ring?





-- minL :: [a] -> [b] -> [(a, b)]
-- maxL :: [a] -> [b] -> [These a b]
-- addL :: [a] -> [b] -> [Either a b]

-- instance ZippySemigroupal [] where (<&>) = zip
-- instance ZippyMonoidal [] where fmax x = repeat x
-- 
-- instance AdditiveSemigroupal [] where (<+>) = zip
-- instance AdditiveMonoidal [] where fzero x = []
-- 
-- instance Additive'Semigroupal [] where (<|>) = these
-- instance Additive'Monoidal [] where fmin x = []
-- 
-- instance Semigroupal [] where (<*>) = concat
-- instance Monoidal [] where fone x = [x]



-- lukajcb says that 'Alt' and 'Alternative' are 'AdditiveSemigroupal'
-- and 'AdditiveMonoidal', respectively. Does this mean that 'ZipList'
-- should be 'Alternative'? The Prelude uses a strange definition.
-- 
-- lukajcb says that 'Alt' and 'Alternative' are 'AdditiveSemigroupal'
-- and 'AdditiveMonoidal', respectively. Is this true? Check the laws.
