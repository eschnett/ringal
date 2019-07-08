module ELLaws where

import Ringal

import Test.QuickCheck
import Test.QuickCheck.Instances()
import Test.QuickCheck.Poly



cmp :: (Eq a, Show a) => Law a -> Property
cmp (Equal x y) = x === y



prop_fadd_assoc_EitherList ::
  EitherList A -> EitherList B -> EitherList C -> Property
prop_fadd_assoc_EitherList xs ys zs = cmp $ law_fadd_assoc xs ys zs

prop_fadd_idLeft_EitherList :: EitherList A -> Property
prop_fadd_idLeft_EitherList xs = cmp $ law_fadd_idLeft xs

prop_fadd_idRight_EitherList :: EitherList A -> Property
prop_fadd_idRight_EitherList xs = cmp $ law_fadd_idRight xs



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

prop_distLeft_EL :: EL A -> EL B -> EL C -> Property
prop_distLeft_EL xs ys zs = cmp $ law_distLeft xs ys zs

prop_distRight_EL :: EL A -> EL B -> EL C -> Property
prop_distRight_EL xs ys zs = cmp $ law_distRight xs ys zs
