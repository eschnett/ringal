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



prop_fadd_assoc_TheseList ::
  TheseList A -> TheseList B -> TheseList C -> Property
prop_fadd_assoc_TheseList xs ys zs = cmp $ law_fadd_assoc xs ys zs

prop_fadd_idLeft_TheseList :: TheseList A -> Property
prop_fadd_idLeft_TheseList xs = cmp $ law_fadd_idLeft xs

prop_fadd_idRight_TheseList :: TheseList A -> Property
prop_fadd_idRight_TheseList xs = cmp $ law_fadd_idRight xs



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

-- > prop_distLeft_EL :: EL A -> EL B -> EL C -> Property
-- > prop_distLeft_EL xs ys zs = cmp $ law_distLeft xs ys zs
-- > 
-- > prop_distRight_EL :: EL A -> EL B -> EL C -> Property
-- > prop_distRight_EL xs ys zs = cmp $ law_distRight xs ys zs



prop_fadd_assoc_TL :: TL A -> TL B -> TL C -> Property
prop_fadd_assoc_TL xs ys zs = cmp $ law_fadd_assoc xs ys zs

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

-- > prop_distLeft_TL :: TL A -> TL B -> TL C -> Property
-- > prop_distLeft_TL xs ys zs = cmp $ law_distLeft xs ys zs
-- > 
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

-- prop_distLeft_EZ :: EZ A -> EZ B -> EZ C -> Property
-- prop_distLeft_EZ xs ys zs = cmp $ law_distLeft xs ys zs
-- 
-- prop_distRight_EZ :: EZ A -> EZ B -> EZ C -> Property
-- prop_distRight_EZ xs ys zs = cmp $ law_distRight xs ys zs



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
