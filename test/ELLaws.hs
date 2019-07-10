{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module ELLaws where

import Ringal hiding (A)

import Test.QuickCheck
import Test.QuickCheck.Instances()
import Test.QuickCheck.Poly



cmp :: (Eq a, Show a) => Law a -> Property
cmp (Equal x y) = x === y

fcmp :: (Eq b, Show b) => Law (a -> b) -> a -> Property
fcmp (Equal x y) a = x a === y a



prop_fadd_assoc_EitherList ::
  EitherList A -> EitherList B -> EitherList C -> Property
prop_fadd_assoc_EitherList xs ys zs = cmp $ law_fadd_assoc xs ys zs

prop_fadd_idLeft_EitherList :: EitherList A -> Property
prop_fadd_idLeft_EitherList xs = cmp $ law_fadd_idLeft xs

prop_fadd_idRight_EitherList :: EitherList A -> Property
prop_fadd_idRight_EitherList xs = cmp $ law_fadd_idRight xs



prop_fadd_assoc_TheseList ::
  TheseList A -> TheseList B -> TheseList C -> Property
prop_fadd_assoc_TheseList xs ys zs = cmp $ law_fadd_assoc xs ys zs

prop_fadd_comm_TheseList :: TheseList A -> TheseList B -> Property
prop_fadd_comm_TheseList xs ys = cmp $ law_fadd_comm xs ys

prop_fadd_idLeft_TheseList :: TheseList A -> Property
prop_fadd_idLeft_TheseList xs = cmp $ law_fadd_idLeft xs

prop_fadd_idRight_TheseList :: TheseList A -> Property
prop_fadd_idRight_TheseList xs = cmp $ law_fadd_idRight xs



prop_fmul_assoc_ZipList :: ZipList A -> ZipList B -> ZipList C -> Property
prop_fmul_assoc_ZipList xs ys zs = cmp $ law_fmul_assoc xs ys zs

prop_fmul_comm_ZipList :: ZipList A -> ZipList B -> Property
prop_fmul_comm_ZipList xs ys = cmp $ law_fmul_comm xs ys

prop_fmul_idLeft_ZipList :: ZipList A -> Property
prop_fmul_idLeft_ZipList xs = cmp $ law_fmul_idLeft xs

prop_fmul_idRight_ZipList :: ZipList A -> Property
prop_fmul_idRight_ZipList xs = cmp $ law_fmul_idRight xs

prop_fmul_absLeft_ZipList :: ZipList A -> Property
prop_fmul_absLeft_ZipList xs = cmp $ law_fmul_absLeft xs

prop_fmul_absRight_ZipList :: ZipList A -> Property
prop_fmul_absRight_ZipList xs = cmp $ law_fmul_absRight xs



prop_fmul_assoc_List :: [] A -> [] B -> [] C -> Property
prop_fmul_assoc_List xs ys zs = cmp $ law_fmul_assoc xs ys zs

prop_fmul_idLeft_List :: [] A -> Property
prop_fmul_idLeft_List xs = cmp $ law_fmul_idLeft xs

prop_fmul_idRight_List :: [] A -> Property
prop_fmul_idRight_List xs = cmp $ law_fmul_idRight xs

prop_fmul_absLeft_List :: [] A -> Property
prop_fmul_absLeft_List xs = cmp $ law_fmul_absLeft xs

prop_fmul_absRight_List :: [] A -> Property
prop_fmul_absRight_List xs = cmp $ law_fmul_absRight xs



prop_fmul_assoc_Function :: Fun C A -> Fun C B -> Fun C C -> C -> Property
prop_fmul_assoc_Function (Fn xs) (Fn ys) (Fn zs) =
  fcmp $ law_fmul_assoc xs ys zs

prop_fmul_comm_Function :: Fun C A -> Fun C B -> C -> Property
prop_fmul_comm_Function (Fn xs) (Fn ys) = fcmp $ law_fmul_comm xs ys

prop_fmul_idLeft_Function :: Fun C A -> C -> Property
prop_fmul_idLeft_Function (Fn xs) = fcmp $ law_fmul_idLeft xs

prop_fmul_idRight_Function :: Fun C A -> C -> Property
prop_fmul_idRight_Function (Fn xs) = fcmp $ law_fmul_idRight xs

prop_fmul_absLeft_Function :: Fun C A -> C -> Property
prop_fmul_absLeft_Function (Fn xs) = fcmp $ law_fmul_absLeft xs

prop_fmul_absRight_Function :: Fun C A -> C -> Property
prop_fmul_absRight_Function (Fn xs) = fcmp $ law_fmul_absRight xs



--------------------------------------------------------------------------------



prop_fadd_assoc_EL :: EL A -> EL B -> EL C -> Property
prop_fadd_assoc_EL xs ys zs = cmp $ law_fadd_assoc xs ys zs

prop_fadd_idLeft_EL :: EL A -> Property
prop_fadd_idLeft_EL xs = cmp $ law_fadd_idLeft xs

prop_fadd_idRight_EL :: EL A -> Property
prop_fadd_idRight_EL xs = cmp $ law_fadd_idRight xs

prop_fmul_assoc_EL :: EL A -> EL B -> EL C -> Property
prop_fmul_assoc_EL xs ys zs = cmp $ law_fmul_assoc xs ys zs

prop_fmul_idLeft_EL :: EL A -> Property
prop_fmul_idLeft_EL xs = cmp $ law_fmul_idLeft xs

prop_fmul_idRight_EL :: EL A -> Property
prop_fmul_idRight_EL xs = cmp $ law_fmul_idRight xs

prop_fmul_absLeft_EL :: EL A -> Property
prop_fmul_absLeft_EL xs = cmp $ law_fmul_absLeft xs

prop_fmul_absRight_EL :: EL A -> Property
prop_fmul_absRight_EL xs = cmp $ law_fmul_absRight xs



prop_fadd_assoc_TL :: TL A -> TL B -> TL C -> Property
prop_fadd_assoc_TL xs ys zs = cmp $ law_fadd_assoc xs ys zs

prop_fadd_comm_TL :: TL A -> TL B -> Property
prop_fadd_comm_TL xs ys = cmp $ law_fadd_comm xs ys

prop_fadd_idLeft_TL :: TL A -> Property
prop_fadd_idLeft_TL xs = cmp $ law_fadd_idLeft xs

prop_fadd_idRight_TL :: TL A -> Property
prop_fadd_idRight_TL xs = cmp $ law_fadd_idRight xs

prop_fmul_assoc_TL :: TL A -> TL B -> TL C -> Property
prop_fmul_assoc_TL xs ys zs = cmp $ law_fmul_assoc xs ys zs

prop_fmul_idLeft_TL :: TL A -> Property
prop_fmul_idLeft_TL xs = cmp $ law_fmul_idLeft xs

prop_fmul_idRight_TL :: TL A -> Property
prop_fmul_idRight_TL xs = cmp $ law_fmul_idRight xs

prop_fmul_absLeft_TL :: TL A -> Property
prop_fmul_absLeft_TL xs = cmp $ law_fmul_absLeft xs

prop_fmul_absRight_TL :: TL A -> Property
prop_fmul_absRight_TL xs = cmp $ law_fmul_absRight xs

prop_distLeft_TL :: TL A -> TL B -> TL C -> Property
prop_distLeft_TL xs ys zs = cmp $ law_distLeft xs ys zs

-- > prop_distRight_TL :: TL A -> TL B -> TL C -> Property
-- > prop_distRight_TL xs ys zs = cmp $ law_distRight xs ys zs



prop_fadd_assoc_EZ :: EZ A -> EZ B -> EZ C -> Property
prop_fadd_assoc_EZ xs ys zs = cmp $ law_fadd_assoc xs ys zs

prop_fadd_idLeft_EZ :: EZ A -> Property
prop_fadd_idLeft_EZ xs = cmp $ law_fadd_idLeft xs

prop_fadd_idRight_EZ :: EZ A -> Property
prop_fadd_idRight_EZ xs = cmp $ law_fadd_idRight xs

prop_fmul_assoc_EZ :: EZ A -> EZ B -> EZ C -> Property
prop_fmul_assoc_EZ xs ys zs = cmp $ law_fmul_assoc xs ys zs

prop_fmul_idLeft_EZ :: EZ A -> Property
prop_fmul_idLeft_EZ xs = cmp $ law_fmul_idLeft xs

prop_fmul_idRight_EZ :: EZ A -> Property
prop_fmul_idRight_EZ xs = cmp $ law_fmul_idRight xs

prop_fmul_absLeft_EZ :: EZ A -> Property
prop_fmul_absLeft_EZ xs = cmp $ law_fmul_absLeft xs

prop_fmul_absRight_EZ :: EZ A -> Property
prop_fmul_absRight_EZ xs = cmp $ law_fmul_absRight xs



prop_fadd_assoc_TZ :: TZ A -> TZ B -> TZ C -> Property
prop_fadd_assoc_TZ xs ys zs = cmp $ law_fadd_assoc xs ys zs

prop_fadd_idLeft_TZ :: TZ A -> Property
prop_fadd_idLeft_TZ xs = cmp $ law_fadd_idLeft xs

prop_fadd_idRight_TZ :: TZ A -> Property
prop_fadd_idRight_TZ xs = cmp $ law_fadd_idRight xs

prop_fmul_assoc_TZ :: TZ A -> TZ B -> TZ C -> Property
prop_fmul_assoc_TZ xs ys zs = cmp $ law_fmul_assoc xs ys zs

prop_fmul_idLeft_TZ :: TZ A -> Property
prop_fmul_idLeft_TZ xs = cmp $ law_fmul_idLeft xs

prop_fmul_idRight_TZ :: TZ A -> Property
prop_fmul_idRight_TZ xs = cmp $ law_fmul_idRight xs

prop_fmul_absLeft_TZ :: TZ A -> Property
prop_fmul_absLeft_TZ xs = cmp $ law_fmul_absLeft xs

prop_fmul_absRight_TZ :: TZ A -> Property
prop_fmul_absRight_TZ xs = cmp $ law_fmul_absRight xs

prop_distLeft_TZ :: TZ A -> TZ B -> TZ C -> Property
prop_distLeft_TZ xs ys zs = cmp $ law_distLeft xs ys zs

prop_distRight_TZ :: TZ A -> TZ B -> TZ C -> Property
prop_distRight_TZ xs ys zs = cmp $ law_distRight xs ys zs
