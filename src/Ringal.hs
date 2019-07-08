-- {-# LANGUAGE DerivingVia #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE TypeSynonymInstances #-}

module Ringal where

import qualified Prelude
import Prelude hiding ( Applicative(..)
                      , Foldable(..)
                      , Functor(..)
                      , Monoid(..)
                      , Num(..)
                      , Semigroup(..)
                      , map)

import Data.Coerce
import Data.Kind
import Data.These hiding (assoc, reassoc, swap)
import Data.Void
import GHC.Generics hiding (S)
import GHC.Natural
import Test.QuickCheck



data Law a = Equal a a
  deriving (Eq, Ord, Read, Show)



class AdditiveSemigroup a where
  (+) :: a -> a -> a

law_add_assoc :: AdditiveSemigroup a => a -> a -> a -> Law a
law_add_assoc x y z = Equal ((x + y) + z) (x + (y + z))

class AdditiveSemigroup a => AdditiveCommutative a

law_add_comm :: AdditiveSemigroup a => a -> a -> Law a
law_add_comm x y = Equal (x + y) (y + x)

class AdditiveSemigroup a => AdditiveMonoid a where
  zero :: a

law_add_idLeft :: AdditiveMonoid a => a -> Law a
law_add_idLeft x = Equal x (zero + x)

law_add_idRight :: AdditiveMonoid a => a -> Law a
law_add_idRight x = Equal x (x + zero)

class AdditiveMonoid a => AdditiveGroup a where
  negate :: a -> a

law_add_invLeft :: AdditiveGroup a => a -> Law a
law_add_invLeft x = Equal zero (negate x + x)

law_add_invRight :: AdditiveGroup a => a -> Law a
law_add_invRight x = Equal zero (x + negate x)



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

law_distleft :: Semiring a => a -> a -> a -> Law a
law_distleft x y z = Equal (x * (y + z)) (x * y + x * z)

law_distright :: Semiring a => a -> a -> a -> Law a
law_distright x y z = Equal ((x + y) * z) (x * z + y * z)

law_absLeft :: Semiring a => a -> Law a
law_absLeft x = Equal zero (zero * x)

law_absRight :: Semiring a => a -> Law a
law_absRight x = Equal zero (x * zero)

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



class Functor f => AdditiveSemigroupal f where
  -- (<+>) :: Product f f ~~> f
  type S f a b :: Type
  (<+>) :: f a -> f b -> f (S f a b)
  infixl 3 <+>
  assocS :: S f (S f a b) c -> S f a (S f b c)
  reassocS :: S f a (S f b c) -> S f (S f a b) c

law_fadd_assoc :: forall f a b c. AdditiveSemigroupal f
                => f a -> f b -> f c -> Law (f (S f (S f a b) c))
law_fadd_assoc xs ys zs =
  Equal ((xs <+> ys) <+> zs) (map (reassocS @f @a @b @c) (xs <+> (ys <+> zs)))

class AdditiveSemigroupal f => AdditiveCommutatival f where
  swapS :: S f a b -> S f b a

law_fadd_comm :: forall f a b. AdditiveCommutatival f
               => f a -> f b -> Law (f (S f a b))
law_fadd_comm xs ys = Equal (xs <+> ys) (map (swapS @f @b @a) (ys <+> xs))

class AdditiveSemigroupal f => AdditiveMonoidal f where
  type Z f :: Type
  empty :: f (Z f)
  unitLeftS :: a -> S f (Z f) a
  reunitLeftS :: S f (Z f) a -> a
  unitRightS :: a -> S f a (Z f)
  reunitRightS :: S f a (Z f) -> a

law_fadd_idLeft :: forall f a. AdditiveMonoidal f
                 => f a -> Law (f a)
law_fadd_idLeft xs = Equal xs (map (reunitLeftS @f @a) (empty <+> xs))

law_fadd_idRight :: forall f a. AdditiveMonoidal f
                  => f a -> Law (f a)
law_fadd_idRight xs = Equal xs (map (reunitRightS @f @a) (xs <+> empty))

class AdditiveSemigroupal f => AdditiveAbsorbal f where
  type Inf f :: Type
  infinity :: f (Inf f)
  zeroLeftS :: f (S f (Inf f) a)
  absurdLeftS :: S f (Inf f) a -> Inf f
  zeroRightS :: f (S f a (Inf f))
  absurdRightS :: S f a (Inf f) -> Inf f

law_fadd_absLeft :: forall f a. AdditiveAbsorbal f
                  => f a -> Law (f (Inf f))
law_fadd_absLeft xs =
  Equal infinity (map (absurdLeftS @f @a) (infinity <+> xs))

law_fadd_absRight :: forall f a. AdditiveAbsorbal f
                   => f a -> Law (f (Inf f))
law_fadd_absRight xs =
  Equal infinity (map (absurdRightS @f @a) (xs <+> infinity))



class Functor f => Semigroupal f where
  -- (<*>) :: Product f f ~~> f
  type P f a b :: Type
  (<*>) :: f a -> f b -> f (P f a b)
  infixl 4 <*>
  assocP :: P f (P f a b) c -> P f a (P f b c)
  reassocP :: P f a (P f b c) -> P f (P f a b) c

law_fmul_assoc :: forall f a b c. Semigroupal f
                => f a -> f b -> f c -> Law (f (P f (P f a b) c))
law_fmul_assoc xs ys zs =
  Equal ((xs <*> ys) <*> zs) (map (reassocP @f @a @b @c) (xs <*> (ys <*> zs)))

class Semigroupal f => Commutatival f where
  swapP :: P f a b -> P f b a

law_fmul_comm :: forall f a b. Commutatival f
               => f a -> f b -> Law (f (P f a b))
law_fmul_comm xs ys = Equal (xs <*> ys) (map (swapP @f @b @a) (ys <*> xs))

class Semigroupal f => Monoidal f where
  type U f :: Type
  unit :: f (U f)
  unitLeftP :: a -> P f (U f) a
  reunitLeftP :: P f (U f) a -> a
  unitRightP :: a -> P f a (U f)
  reunitRightP :: P f a (U f) -> a

law_fmul_idLeft :: forall f a. Monoidal f
                 => f a -> Law (f a)
law_fmul_idLeft xs = Equal xs (map (reunitLeftP @f @a) (unit <*> xs))

law_fmul_idRight :: forall f a. Monoidal f
                  => f a -> Law (f a)
law_fmul_idRight xs = Equal xs (map (reunitRightP @f @a) (xs <*> unit))

class Semigroupal f => Absorbal f where
  -- | In a Semiringal, this should be identital to 'Z' of the
  -- 'AdditiveMonoidal'
  type ZeroP f :: Type
  zeroP :: f (ZeroP f)
  zeroLeftP :: f (P f (ZeroP f) a)
  absurdLeftP :: P f (ZeroP f) a -> ZeroP f
  zeroRightP :: f (P f a (ZeroP f))
  absurdRightP :: P f a (ZeroP f) -> ZeroP f

law_fmul_absLeft :: forall f a. Absorbal f
                  => f a -> Law (f (ZeroP f))
law_fmul_absLeft xs =
  Equal zeroP (map (absurdLeftP @f @a) (zeroP <*> xs))

law_fmul_absRight :: forall f a. Absorbal f
                   => f a -> Law (f (ZeroP f))
law_fmul_absRight xs =
  Equal zeroP (map (absurdRightP @f @a) (xs <*> zeroP))



class (AdditiveMonoidal f, Monoidal f, Absorbal f, ZeroP f ~ Z f) =>
      Semiringal f where
  distLeft :: P f a (S f b c) -> S f (P f a b) (P f a c)
  distRight :: P f (S f a b) c -> S f (P f a c) (P f b c)

law_distLeft :: forall f a b c. Semiringal f
             => f a -> f b -> f c -> Law (f (S f (P f a b) (P f a c)))
law_distLeft xs ys zs =
  Equal
  (map (distLeft @f @a @b @c) (xs <*> (ys <+> zs)))
  (xs <*> ys <+> xs <*> zs)

law_distRight :: forall f a b c. Semiringal f
             => f a -> f b -> f c -> Law (f (S f (P f a c) (P f b c)))
law_distRight xs ys zs =
  Equal
  (map (distRight @f @a @b @c) ((xs <+> ys) <*> zs))
  (xs <*> zs <+> ys <*> zs)

class (Semiringal f, AdditiveCommutatival f) => Ringal f



--------------------------------------------------------------------------------



instance AdditiveSemigroup [a] where (+) = (++)
instance AdditiveMonoid [a] where zero = []



newtype EitherList a = EitherList { getEitherList :: [a] }
  deriving (Eq, Ord, Read, Show)
  deriving Arbitrary via [a]
  deriving (Foldable, Functor) via []

instance AdditiveSemigroupal EitherList where
  type S EitherList a b = Either a b
  EitherList (x:xs) <+> ys = EitherList (Left x : rs)
    where EitherList rs = EitherList xs <+> ys
  EitherList [] <+> EitherList (y:ys) = EitherList (Right y : rs)
    where EitherList rs = EitherList [] <+> EitherList ys
  EitherList _ <+> EitherList _ = EitherList []
  assocS (Left (Left x)) = Left x
  assocS (Left (Right y)) = Right (Left y)
  assocS (Right z) = Right (Right z)
  reassocS (Left x) = Left (Left x)
  reassocS (Right (Left y)) = Left (Right y)
  reassocS (Right (Right z)) = Right z

instance AdditiveMonoidal EitherList where
  type Z EitherList = Void
  empty = EitherList []
  unitLeftS x = Right x
  reunitLeftS (Left _) = undefined -- impossible
  reunitLeftS (Right x) = x
  unitRightS x = Left x
  reunitRightS (Left x) = x
  reunitRightS (Right _) = undefined -- impossible



newtype TheseList a = TheseList { getTheseList :: [a] }
  deriving (Eq, Ord, Read, Show)
  deriving (Foldable, Functor) via []

instance AdditiveSemigroupal TheseList where
  type S TheseList a b = These a b
  TheseList (x:xs) <+> TheseList (y:ys) = TheseList (These x y : rs)
    where TheseList rs = TheseList xs <+> TheseList ys
  TheseList (x:xs) <+> TheseList [] = TheseList (This x : rs)
    where TheseList rs = TheseList xs <+> TheseList []
  TheseList [] <+> TheseList (y:ys) = TheseList (That y : rs)
    where TheseList rs = TheseList [] <+> TheseList ys
  TheseList _ <+> TheseList _ = TheseList []
  assocS (This (This x))       = This x
  assocS (This (That y))       = That (This y)
  assocS (That z)              = That (That z)
  assocS (These (That y) z)    = That (These y z)
  assocS (This (These x y))    = These x (This y)
  assocS (These (This x) z)    = These x (That z)
  assocS (These (These x y) z) = These x (These y z)
  reassocS (This x)              = This (This x)
  reassocS (That (This y))       = This (That y)
  reassocS (That (That z))       = That z
  reassocS (That (These y z))    = These (That y) z
  reassocS (These x (This y))    = This (These x y)
  reassocS (These x (That z))    = These (This x) z
  reassocS (These x (These y z)) = These (These x y) z

instance AdditiveCommutatival TheseList where
  swapS (This x)    = That x
  swapS (That y)    = This y
  swapS (These x y) = These y x

instance AdditiveMonoidal TheseList where
  type Z TheseList = Void
  empty = TheseList []
  unitLeftS x = That x
  reunitLeftS (This _) = undefined -- impossible
  reunitLeftS (That x) = x
  reunitLeftS (These _ _) = undefined -- impossible
  unitRightS x = This x
  reunitRightS (This x) = x
  reunitRightS (That _) = undefined    -- impossible
  reunitRightS (These _ _) = undefined -- impossible



newtype ZipList a = ZipList { getZipList :: [a] }
  deriving (Eq, Ord, Read, Show)
  deriving (Foldable, Functor) via []

instance Semigroupal ZipList where
  type P ZipList a b = (a, b)
  ZipList (x:xs) <*> ZipList (y:ys) = ZipList ((x,y) : rs)
    where ZipList rs = ZipList xs <*> ZipList ys
  ZipList _ <*> ZipList _ = ZipList []
  assocP ((x, y), z) = (x, (y, z))
  reassocP (x, (y, z)) = ((x, y), z)

instance Commutatival ZipList where
  swapP (x, y) = (y, x)

instance Monoidal ZipList where
  type U ZipList = ()
  unit = ZipList (repeat ())
  unitLeftP x = ((), x)
  reunitLeftP (_, x) = x
  unitRightP x = (x, ())
  reunitRightP (x, _) = x

instance Absorbal ZipList where
  type ZeroP ZipList = Void
  zeroP = ZipList []
  zeroLeftP = ZipList []
  absurdLeftP (z, _) = absurd z
  zeroRightP = ZipList []
  absurdRightP (_, z) = absurd z



instance Semigroupal [] where
  type P [] a b = (a, b)
  xs <*> ys = [(x, y) | x <- xs, y <- ys]
  assocP ((x, y), z) = (x, (y, z))
  reassocP (x, (y, z)) = ((x, y), z)

instance Monoidal [] where
  type U [] = ()
  unit = [()]
  unitLeftP x = ((), x)
  reunitLeftP (_, x) = x
  unitRightP x = (x, ())
  reunitRightP (x, _) = x

instance Absorbal [] where
  type ZeroP [] = Void
  zeroP = []
  zeroLeftP = []
  absurdLeftP (z, _) = absurd z
  zeroRightP = []
  absurdRightP (_, z) = absurd z



--------------------------------------------------------------------------------



coerce1 :: forall s t a b. (Coercible s a, Coercible t b) => (a -> b) -> s -> t
coerce1 f x = coerce (f (coerce x))

coerce2 :: forall s t u a b c. (Coercible s a, Coercible t b, Coercible u c)
        => (a -> b -> c) -> s -> t -> u
coerce2 f x y = coerce (f (coerce x) (coerce y))

coerceF :: forall f g a. Coercible (f a) (g a) => f a -> g a
coerceF = coerce

coerceF1 :: forall f g a b. (Coercible (f a) (g a), Coercible (f b) (g b))
         => (f a -> f b) -> g a -> g b
coerceF1 f x = coerce (f (coerce x))

coerceF2 :: forall f g a b c.
            ( Coercible (f a) (g a)
            , Coercible (f b) (g b)
            , Coercible (f c) (g c)
            )
         => (f a -> f b -> f c) -> g a -> g b -> g c
coerceF2 f x y = coerce (f (coerce x) (coerce y))



newtype EL a = EL [a]
  deriving (Eq, Ord, Read, Show, Generic)
  deriving Arbitrary via [a]
  deriving (Foldable, Functor) via []

instance AdditiveSemigroupal EL where
  type S EL a b = S EitherList a b
  (<+>) = coerceF2 @EitherList (<+>)
  assocS :: forall a b c. Either (Either a b) c -> Either a (Either b c)
  assocS = coerce1 (assocS @EitherList @a @b @c)
  reassocS :: forall a b c. Either a (Either b c) -> Either (Either a b) c
  reassocS = coerce1 (reassocS @EitherList @a @b @c)

instance AdditiveMonoidal EL where
  type Z EL = Z EitherList
  empty = coerce (empty @EitherList)
  unitLeftS x = coerce (unitLeftS @EitherList x)
  reunitLeftS x = reunitLeftS @EitherList (coerce x)
  unitRightS x = coerce (unitRightS @EitherList x)
  reunitRightS x = reunitRightS @EitherList (coerce x)

instance Semigroupal EL where
  type P EL a b = P [] a b
  (<*>) = coerceF2 @[] (<*>)
  assocP :: forall a b c. (,) ((,) a b) c -> (,) a ((,) b c)
  assocP = coerce1 (assocP @[] @a @b @c)
  reassocP :: forall a b c. (,) a ((,) b c) -> (,) ((,) a b) c
  reassocP = coerce1 (reassocP @[] @a @b @c)

instance Monoidal EL where
  type U EL = U []
  unit = coerce (unit @[])
  unitLeftP x = coerce (unitLeftP @[] x)
  reunitLeftP x = reunitLeftP @[] (coerce x)
  unitRightP x = coerce (unitRightP @[] x)
  reunitRightP x = reunitRightP @[] (coerce x)

instance Absorbal EL where
  type ZeroP EL = ZeroP []
  zeroP = coerce (zeroP @[])
  zeroLeftP :: forall a. EL (P EL (ZeroP EL) a)
  zeroLeftP = coerce (zeroLeftP @[] @a)
  absurdLeftP :: forall a. P EL (ZeroP EL) a -> ZeroP EL
  absurdLeftP x = coerce (absurdLeftP @[] @a (coerce x))
  zeroRightP :: forall a. EL (P EL a (ZeroP EL))
  zeroRightP = coerce (zeroRightP @[] @a)
  absurdRightP :: forall a. P EL a (ZeroP EL) -> ZeroP EL
  absurdRightP x = coerce (absurdRightP @[] @a (coerce x))

-- These laws do not hold
-- > instance Semiringal EL where
-- >   distLeft (x, Left y) = Left (x, y)
-- >   distLeft (x, Right z) = Right (x, z)
-- >   distRight (Left x, z) = Left (x, z)
-- >   distRight (Right y, z) = Right (y, z)



--------------------------------------------------------------------------------



-- > law_length_zip :: (ZippyMonoidal f, Foldable f) => f a -> f b -> Law Int
-- > law_length_zip xs ys = Equal (min (length xs) (length ys)) (length (xs <&> ys))

-- > law_length_add :: (AdditiveMonoidal f, Foldable f) => f a -> f b -> Law Int
-- > law_length_add xs ys = Equal (length xs + length ys) (length (xs <+> ys))

-- > law_length_mul :: (Monoidal f, Foldable f) => f a -> f b -> Law Int
-- > law_length_mul xs ys = Equal (length xs * length ys) (length (xs <*> ys))



-- minL :: [a] -> [b] -> [(a, b)]
-- maxL :: [a] -> [b] -> [These a b]
-- addL :: [a] -> [b] -> [Either a b]
-- mulL :: [a] -> [b] -> [(a, b)]


-- Type         Prod     Unit        Abs   Length

-- EitherList   Either   []          n/a   (+)
-- TheseList    These    []          n/a   max
-- ZipList      (,)      repeat ()   []    min
-- []           (,)      [()]        []    (*)

-- Observations:

-- [] is not symmetric. Right distributivity works, but left
-- distributivity does not.

-- Either-[]:   x * (y + z) = x * y + x * z

-- These-[]:   x * (max y z) = max (x * y) (x * z)

-- Zip-Either:   min x (y + z) = min x y + min x z

-- Zip-These:   min x (max y z) = max (min x y) (min x z)



-- lukajcb says that 'Alt' and 'Alternative' are 'AdditiveSemigroupal'
-- and 'AdditiveMonoidal', respectively. Does this mean that 'ZipList'
-- should be 'Alternative'? The Prelude uses a strange definition.
-- 
-- lukajcb says that 'Alt' and 'Alternative' are 'AdditiveSemigroupal'
-- and 'AdditiveMonoidal', respectively. Is this true? Check the laws.
