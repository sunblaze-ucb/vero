import ArithmeticV2.Impl.Internals.GeneralInternals
import ArithmeticV2.Impl.Internals.MulInternals
import ArithmeticV2.Impl.Internals.ModInternalsNonlinear
import ArithmeticV2.Impl.Internals.ModInternals
import ArithmeticV2.Impl.Internals.DivInternals
import ArithmeticV2.Impl.Internals.DivInternalsNonlinear
import ArithmeticV2.Impl.DivMod
import ArithmeticV2.Impl.Mul
import ArithmeticV2.Impl.Power
import ArithmeticV2.Impl.Power2
import ArithmeticV2.Impl.Logarithm
import ArithmeticV2.Impl.Overflow
import ArithmeticV2.Impl.Internals.MulInternalsNonlinear

/-!
# ArithmeticV2.Bundle

Per-package implementation bundle for the `ArithmeticV2` root package.
Collects all scored API signatures into one structure.

DO NOT MODIFY -- benchmark infrastructure.
-/

structure ArithmeticV2Bundle where
  CheckedU128_new : ArithmeticV2.CheckedU128NewSig
  CheckedU16_new : ArithmeticV2.CheckedU16NewSig
  CheckedU32_new : ArithmeticV2.CheckedU32NewSig
  CheckedU64_new : ArithmeticV2.CheckedU64NewSig
  CheckedU8_new : ArithmeticV2.CheckedU8NewSig
  CheckedUsize_new : ArithmeticV2.CheckedUsizeNewSig
  CheckedU128_new_overflowed : ArithmeticV2.CheckedU128NewOverflowedSig
  CheckedU16_new_overflowed : ArithmeticV2.CheckedU16NewOverflowedSig
  CheckedU32_new_overflowed : ArithmeticV2.CheckedU32NewOverflowedSig
  CheckedU64_new_overflowed : ArithmeticV2.CheckedU64NewOverflowedSig
  CheckedU8_new_overflowed : ArithmeticV2.CheckedU8NewOverflowedSig
  CheckedUsize_new_overflowed : ArithmeticV2.CheckedUsizeNewOverflowedSig
  CheckedU128_is_overflowed : ArithmeticV2.CheckedU128IsOverflowedSig
  CheckedU16_is_overflowed : ArithmeticV2.CheckedU16IsOverflowedSig
  CheckedU32_is_overflowed : ArithmeticV2.CheckedU32IsOverflowedSig
  CheckedU64_is_overflowed : ArithmeticV2.CheckedU64IsOverflowedSig
  CheckedU8_is_overflowed : ArithmeticV2.CheckedU8IsOverflowedSig
  CheckedUsize_is_overflowed : ArithmeticV2.CheckedUsizeIsOverflowedSig
  CheckedU128_unwrap : ArithmeticV2.CheckedU128UnwrapSig
  CheckedU16_unwrap : ArithmeticV2.CheckedU16UnwrapSig
  CheckedU32_unwrap : ArithmeticV2.CheckedU32UnwrapSig
  CheckedU64_unwrap : ArithmeticV2.CheckedU64UnwrapSig
  CheckedU8_unwrap : ArithmeticV2.CheckedU8UnwrapSig
  CheckedUsize_unwrap : ArithmeticV2.CheckedUsizeUnwrapSig
  CheckedU128_to_option : ArithmeticV2.CheckedU128ToOptionSig
  CheckedU16_to_option : ArithmeticV2.CheckedU16ToOptionSig
  CheckedU32_to_option : ArithmeticV2.CheckedU32ToOptionSig
  CheckedU64_to_option : ArithmeticV2.CheckedU64ToOptionSig
  CheckedU8_to_option : ArithmeticV2.CheckedU8ToOptionSig
  CheckedUsize_to_option : ArithmeticV2.CheckedUsizeToOptionSig
  CheckedU128_add_value : ArithmeticV2.CheckedU128AddValueSig
  CheckedU16_add_value : ArithmeticV2.CheckedU16AddValueSig
  CheckedU32_add_value : ArithmeticV2.CheckedU32AddValueSig
  CheckedU64_add_value : ArithmeticV2.CheckedU64AddValueSig
  CheckedU8_add_value : ArithmeticV2.CheckedU8AddValueSig
  CheckedUsize_add_value : ArithmeticV2.CheckedUsizeAddValueSig
  CheckedU128_add_checked : ArithmeticV2.CheckedU128AddCheckedSig
  CheckedU16_add_checked : ArithmeticV2.CheckedU16AddCheckedSig
  CheckedU32_add_checked : ArithmeticV2.CheckedU32AddCheckedSig
  CheckedU64_add_checked : ArithmeticV2.CheckedU64AddCheckedSig
  CheckedU8_add_checked : ArithmeticV2.CheckedU8AddCheckedSig
  CheckedUsize_add_checked : ArithmeticV2.CheckedUsizeAddCheckedSig
  CheckedU128_mul_value : ArithmeticV2.CheckedU128MulValueSig
  CheckedU16_mul_value : ArithmeticV2.CheckedU16MulValueSig
  CheckedU32_mul_value : ArithmeticV2.CheckedU32MulValueSig
  CheckedU64_mul_value : ArithmeticV2.CheckedU64MulValueSig
  CheckedU8_mul_value : ArithmeticV2.CheckedU8MulValueSig
  CheckedUsize_mul_value : ArithmeticV2.CheckedUsizeMulValueSig
  CheckedU128_mul_checked : ArithmeticV2.CheckedU128MulCheckedSig
  CheckedU16_mul_checked : ArithmeticV2.CheckedU16MulCheckedSig
  CheckedU32_mul_checked : ArithmeticV2.CheckedU32MulCheckedSig
  CheckedU64_mul_checked : ArithmeticV2.CheckedU64MulCheckedSig
  CheckedU8_mul_checked : ArithmeticV2.CheckedU8MulCheckedSig
  CheckedUsize_mul_checked : ArithmeticV2.CheckedUsizeMulCheckedSig
