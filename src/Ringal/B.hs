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

module Ringal.B where

import qualified Prelude
import Prelude hiding ( Applicative(..)
                      , Foldable(..)
                      , Functor(..)
                      , Monoid(..)
                      , Num(..)
                      , Semigroup(..)
                      , map)

import Data.Kind
import Data.These hiding (assoc, reassoc, swap)
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



-- newtype f ~> g = Nat (forall a. f a -> g a)
-- newtype f ~~> g = Binat (forall a b. f a b -> g a b)

-- data Sum f g a = InL (f a) | InR (g a)
--   deriving (Eq, Ord, Read, Show)
-- data Product f g a = Product (f a) (g a)
--   deriving (Eq, Ord, Read, Show)
-- data Empty a
-- newtype Unit a = Unit a
--   deriving (Eq, Ord, Read, Show)
-- 
-- instance (Functor f, Functor g) => Functor (Sum f g) where
--   map f (InL xs) = InL (map f xs)
--   map f (InR ys) = InR (map f ys)
-- instance (Functor f, Functor g) => Functor (Product f g) where
--   map f (Product xs ys) = Product (map f xs) (map f ys)
-- instance Functor Empty where
--   map _ _ = undefined
-- instance Functor Unit where
--   map f (Unit x) = Unit (f x)
-- 
-- instance (Foldable f, Foldable g) => Foldable (Sum f g) where
--   length (InL xs) = length xs
--   length (InR ys) = length ys
-- instance (Foldable f, Foldable g) => Foldable (Product f g) where
--   length (Product xs ys) = length xs + length ys
-- instance Foldable Empty where
--   length _ = 0
-- instance Foldable Unit where
--   length _ = 1



--------------------------------------------------------------------------------



-- class Binary p where
--   type Merge p a b :: Type
--   -- run :: (forall x y. r x y ~ Merge p x y) => p -> a -> b -> r a b
--   run :: p -> a -> b -> Merge p a b
-- 
-- class Binary p => Assoc p where
--   -- assoc :: (forall x y. r x y ~ Merge p x y) => r (r a b) c -> r a (r b c)
--   -- reassoc :: (forall x y. r x y ~ Merge p x y) => r a (r b c) -> r (r a b) c
--   assoc :: Merge p (Merge p a b) c -> Merge p a (Merge p b c)
--   reassoc :: Merge p a (Merge p b c) -> Merge p (Merge p a b) c
-- 
-- class Binary p => Comm p where
--   swap :: r a b ~ Merge p a b => r a b -> p b a
-- 
-- class Assoc p => Mon p where
--   type Unit p :: Type
--   leftUnit :: (r a b ~ Merge p a b, u ~ Unit f) => a -> r u a
--   rightUnit :: (r a b ~ Merge p a b, u ~ Unit f) => a -> r a u
-- 
-- 
-- 
-- instance Binary (,) where
--   type Merge (,) a b = (a, b)
--   run = (,)
-- 
-- instance Assoc (,) where
--   assoc ((x, y), z) = (x, (y, z))
--   reassoc (x, (y, z)) = ((x, y), z)
-- 
-- instance Comm (,) where
--   swap (x, y) = (y, x)
-- 
-- instance Mon (,) where
--   type Unit (,) = ()
--   leftUnit x = ((), x)
--   rightUnit x = (x, ())
-- 
-- 
-- 
-- instance Binary These where
--   type Merge These a b = These a b
--   run = These



--------------------------------------------------------------------------------



class Functor f => AdditiveSemigroupal f where
  -- (<+>) :: Product f f ~~> f
  (<+>) :: f a -> f b -> f (a, b)
  (<+>) = liftAdd (,)
  liftAdd :: (a -> b -> c) -> f a -> f b -> f c

prop_fadd_assoc :: forall f a b c. AdditiveSemigroupal f
                => f a -> f b -> f c -> Law (f ((a, b), c))
prop_fadd_assoc xs ys zs =
  Equal ((xs <+> ys) <+> zs) (map reassoc (xs <+> (ys <+> zs)))
  where reassoc (x, (y, z)) = ((x, y), z)

class AdditiveSemigroupal f => AdditiveCommutatival f

prop_fadd_comm :: AdditiveCommutatival f => f a -> f b -> Law (f (a, b))
prop_fadd_comm xs ys = Equal (xs <+> ys) (map swap (ys <+> xs))
  where swap (x, y) = (y, x)

class AdditiveSemigroupal f => AdditiveMonoidal f where
  -- | Technically, this should be 'f Void', but since 'f' is a
  -- functor, we can always map a function 'Void -> a', which is
  -- 'absurd'.
  empty :: a -> f a

prop_fadd_idleft :: AdditiveMonoidal f => f a -> Law (f a)
prop_fadd_idleft xs = Equal xs (map reunitL (empty () <+> xs))
  where reunitL ((), x) = x

prop_fadd_idright :: AdditiveMonoidal f => f a -> Law (f a)
prop_fadd_idright xs = Equal xs (map reunitR (xs <+> empty ()))
  where reunitR (x, ()) = x



class Functor f => Semigroupal f where
  -- (<*>) :: Product f f ~~> f
  (<*>) :: f a -> f b -> f (a, b)
  (<*>) = liftMul (,)
  liftMul :: (a -> b -> c) -> f a -> f b -> f c

prop_fmul_assoc :: forall f a b c. Semigroupal f
                => f a -> f b -> f c -> Law (f ((a, b), c))
prop_fmul_assoc xs ys zs =
  Equal ((xs <*> ys) <*> zs) (map reassoc (xs <*> (ys <*> zs)))
  where reassoc (x, (y, z)) = ((x, y), z)

class Semigroupal f => Commutatival f

prop_fmul_comm :: Commutatival f => f a -> f b -> Law (f (a, b))
prop_fmul_comm xs ys = Equal (xs <*> ys) (map swap (ys <*> xs))
  where swap (x, y) = (y, x)

class Semigroupal f => Monoidal f where
  -- | Technically, this should be 'f ()', but since 'f' is a functor,
  -- we can always map a function '() -> a'. Such a function is
  -- equivalent to a constant.
  unit :: a -> f a

prop_fmul_idleft :: Monoidal f => f a -> Law (f a)
prop_fmul_idleft xs = Equal xs (map reunitL (unit () <*> xs))
  where reunitL ((), x) = x

prop_fmul_idright :: Monoidal f => f a -> Law (f a)
prop_fmul_idright xs = Equal xs (map reunitR (xs <*> unit ()))
  where reunitR (x, ()) = x



--------------------------------------------------------------------------------



instance AdditiveSemigroup [a] where (+) = (++)
instance AdditiveMonoid [a] where zero = []



newtype EitherList a = EitherList { getEitherList :: [a] }
  deriving (Eq, Ord, Read, Show)
  deriving (Foldable, Functor) via []

-- instance AdditiveSemigroupal EitherList where
--   EitherList (x:xs) <+> ys = EitherList (Left x : rs)
--     where EitherList rs = EitherList xs <+> ys
--   EitherList [] <+> EitherList (y:ys) = EitherList (Right y : rs)
--     where EitherList rs = EitherList [] <+> EitherList ys
--   EitherList _ <+> EitherList _ = EitherList []
-- 
-- instance AdditiveCommutatival EitherList
-- 
-- instance AdditiveMonoidal EitherList where
--   empty = EitherList []



-- TODO> newtype TheseList a = TheseList { getTheseList :: [a] }
-- TODO>   deriving (Eq, Ord, Read, Show)
-- TODO>   deriving (Foldable, Functor) via []
-- TODO> 
-- TODO> instance AdditiveSemigroupal TheseList These where
-- TODO>   TheseList (x:xs) <+> TheseList (y:ys) = TheseList (These x y : rs)
-- TODO>     where TheseList rs = TheseList xs <+> TheseList ys
-- TODO>   TheseList (x:xs) <+> TheseList [] = TheseList (This x : rs)
-- TODO>     where TheseList rs = TheseList xs <+> TheseList []
-- TODO>   TheseList [] <+> TheseList (y:ys) = TheseList (That y : rs)
-- TODO>     where TheseList rs = TheseList [] <+> TheseList ys
-- TODO>   TheseList _ <+> TheseList _ = TheseList []
-- TODO> 
-- TODO> instance AdditiveCommutatival TheseList These
-- TODO> 
-- TODO> instance AdditiveMonoidal TheseList These Void where
-- TODO>   absurd = Data.Void.absurd
-- TODO>   empty = TheseList []
-- TODO> 
-- TODO> 
-- TODO> 
-- TODO> newtype ZipList a = ZipList { getZipList :: [a] }
-- TODO>   deriving (Eq, Ord, Read, Show)
-- TODO>   deriving (Foldable, Functor) via []
-- TODO> 
-- TODO> instance Semigroupal ZipList (,) where
-- TODO>   ZipList (x:xs) <*> ZipList (y:ys) = ZipList ((x,y) : rs)
-- TODO>     where ZipList rs = ZipList xs <*> ZipList ys
-- TODO>   ZipList _ <*> ZipList _ = ZipList []
-- TODO> 
-- TODO> instance Commutatival ZipList (,)
-- TODO> 
-- TODO> instance Monoidal ZipList (,) () where
-- TODO>   it = ()
-- TODO>   unit x = ZipList (repeat x)
-- TODO> 
-- TODO> 
-- TODO> 
-- TODO> instance Semigroupal [] (,) where
-- TODO>   xs <*> ys = [(x, y) | x <- xs, y <- ys]
-- TODO> 
-- TODO> instance Monoidal [] (,) () where
-- TODO>   it = ()
-- TODO>   unit x = [x]



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
