import ArithmeticV2.Impl.Overflow

/-!
# ArithmeticV2.Test

Executable conformance tests for the curated reference implementations.

DO NOT MODIFY -- infrastructure.
-/

-- guard_checked_u8_new_to_option: Creating a CheckedU8 from an in-range value preserves that value.
#guard ArithmeticV2.CheckedU8_to_option (ArithmeticV2.CheckedU8_new 7) == some 7

-- guard_checked_u8_new_not_overflowed: A fresh in-range CheckedU8 is not overflowed.
#guard ArithmeticV2.CheckedU8_is_overflowed (ArithmeticV2.CheckedU8_new 7) == false

-- guard_checked_u8_overflowed: A CheckedU8 constructed above the u8 maximum is overflowed.
#guard ArithmeticV2.CheckedU8_is_overflowed (ArithmeticV2.CheckedU8_new_overflowed 256) == true

-- guard_checked_u8_add_value_overflows: Adding past the u8 maximum produces no concrete option.
#guard ArithmeticV2.CheckedU8_to_option (ArithmeticV2.CheckedU8_add_value (ArithmeticV2.CheckedU8_new 255) 1) == none

-- guard_checked_u16_add_checked: Adding two in-range CheckedU16 values preserves their arithmetic sum.
#guard ArithmeticV2.CheckedU16_to_option (ArithmeticV2.CheckedU16_add_checked (ArithmeticV2.CheckedU16_new 200) (ArithmeticV2.CheckedU16_new 300)) == some 500

-- guard_checked_u32_mul_value: Multiplying in range CheckedU32 values preserves their arithmetic product.
#guard ArithmeticV2.CheckedU32_to_option (ArithmeticV2.CheckedU32_mul_value (ArithmeticV2.CheckedU32_new 12) 11) == some 132

-- guard_checked_u64_mul_overflowed_by_zero: Multiplying an overflowed CheckedU64 by zero recovers concrete zero, matching the source branch.
#guard ArithmeticV2.CheckedU64_to_option (ArithmeticV2.CheckedU64_mul_value (ArithmeticV2.CheckedU64_new_overflowed 18446744073709551616) 0) == some 0

-- guard_checked_u128_mul_checked_overflow: Multiplying beyond the u128 maximum overflows.
#guard ArithmeticV2.CheckedU128_is_overflowed (ArithmeticV2.CheckedU128_mul_checked (ArithmeticV2.CheckedU128_new 340282366920938463463374607431768211455) (ArithmeticV2.CheckedU128_new 2)) == true

namespace ArithmeticV2

/- Additional per-API guard coverage for the checked-overflow surface. -/
#guard CheckedU128_to_option (CheckedU128_new 1) == some 1
#guard CheckedU128_is_overflowed (CheckedU128_new_overflowed 340282366920938463463374607431768211456) == true
#guard CheckedU128_is_overflowed (CheckedU128_new 1) == false
#guard CheckedU128_unwrap (CheckedU128_new 1) == 1
#guard CheckedU128_to_option (CheckedU128_new 2) == some 2
#guard CheckedU128_to_option (CheckedU128_add_value (CheckedU128_new 1) 2) == some 3
#guard CheckedU128_to_option (CheckedU128_add_checked (CheckedU128_new 1) (CheckedU128_new 2)) == some 3
#guard CheckedU128_to_option (CheckedU128_mul_value (CheckedU128_new 3) 4) == some 12
#guard CheckedU128_to_option (CheckedU128_mul_checked (CheckedU128_new 3) (CheckedU128_new 4)) == some 12

#guard CheckedU16_to_option (CheckedU16_new 1) == some 1
#guard CheckedU16_is_overflowed (CheckedU16_new_overflowed 65536) == true
#guard CheckedU16_is_overflowed (CheckedU16_new 1) == false
#guard CheckedU16_unwrap (CheckedU16_new 1) == 1
#guard CheckedU16_to_option (CheckedU16_new 2) == some 2
#guard CheckedU16_to_option (CheckedU16_add_value (CheckedU16_new 1) 2) == some 3
#guard CheckedU16_to_option (CheckedU16_add_checked (CheckedU16_new 1) (CheckedU16_new 2)) == some 3
#guard CheckedU16_to_option (CheckedU16_mul_value (CheckedU16_new 3) 4) == some 12
#guard CheckedU16_to_option (CheckedU16_mul_checked (CheckedU16_new 3) (CheckedU16_new 4)) == some 12

#guard CheckedU32_to_option (CheckedU32_new 1) == some 1
#guard CheckedU32_is_overflowed (CheckedU32_new_overflowed 4294967296) == true
#guard CheckedU32_is_overflowed (CheckedU32_new 1) == false
#guard CheckedU32_unwrap (CheckedU32_new 1) == 1
#guard CheckedU32_to_option (CheckedU32_new 2) == some 2
#guard CheckedU32_to_option (CheckedU32_add_value (CheckedU32_new 1) 2) == some 3
#guard CheckedU32_to_option (CheckedU32_add_checked (CheckedU32_new 1) (CheckedU32_new 2)) == some 3
#guard CheckedU32_to_option (CheckedU32_mul_value (CheckedU32_new 3) 4) == some 12
#guard CheckedU32_to_option (CheckedU32_mul_checked (CheckedU32_new 3) (CheckedU32_new 4)) == some 12

#guard CheckedU64_to_option (CheckedU64_new 1) == some 1
#guard CheckedU64_is_overflowed (CheckedU64_new_overflowed 18446744073709551616) == true
#guard CheckedU64_is_overflowed (CheckedU64_new 1) == false
#guard CheckedU64_unwrap (CheckedU64_new 1) == 1
#guard CheckedU64_to_option (CheckedU64_new 2) == some 2
#guard CheckedU64_to_option (CheckedU64_add_value (CheckedU64_new 1) 2) == some 3
#guard CheckedU64_to_option (CheckedU64_add_checked (CheckedU64_new 1) (CheckedU64_new 2)) == some 3
#guard CheckedU64_to_option (CheckedU64_mul_value (CheckedU64_new 3) 4) == some 12
#guard CheckedU64_to_option (CheckedU64_mul_checked (CheckedU64_new 3) (CheckedU64_new 4)) == some 12

#guard CheckedU8_to_option (CheckedU8_new 1) == some 1
#guard CheckedU8_is_overflowed (CheckedU8_new_overflowed 256) == true
#guard CheckedU8_is_overflowed (CheckedU8_new 1) == false
#guard CheckedU8_unwrap (CheckedU8_new 1) == 1
#guard CheckedU8_to_option (CheckedU8_new 2) == some 2
#guard CheckedU8_to_option (CheckedU8_add_value (CheckedU8_new 1) 2) == some 3
#guard CheckedU8_to_option (CheckedU8_add_checked (CheckedU8_new 1) (CheckedU8_new 2)) == some 3
#guard CheckedU8_to_option (CheckedU8_mul_value (CheckedU8_new 3) 4) == some 12
#guard CheckedU8_to_option (CheckedU8_mul_checked (CheckedU8_new 3) (CheckedU8_new 4)) == some 12

#guard CheckedUsize_to_option (CheckedUsize_new 1) == some 1
#guard CheckedUsize_is_overflowed (CheckedUsize_new_overflowed 18446744073709551616) == true
#guard CheckedUsize_is_overflowed (CheckedUsize_new 1) == false
#guard CheckedUsize_unwrap (CheckedUsize_new 1) == 1
#guard CheckedUsize_to_option (CheckedUsize_new 2) == some 2
#guard CheckedUsize_to_option (CheckedUsize_add_value (CheckedUsize_new 1) 2) == some 3
#guard CheckedUsize_to_option (CheckedUsize_add_checked (CheckedUsize_new 1) (CheckedUsize_new 2)) == some 3
#guard CheckedUsize_to_option (CheckedUsize_mul_value (CheckedUsize_new 3) 4) == some 12
#guard CheckedUsize_to_option (CheckedUsize_mul_checked (CheckedUsize_new 3) (CheckedUsize_new 4)) == some 12

end ArithmeticV2
