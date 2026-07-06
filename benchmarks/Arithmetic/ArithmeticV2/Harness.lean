import ArithmeticV2.Bundle

/-!
# ArithmeticV2.Harness

Benchmark harness: `RepoImpl` structure, canonical implementation wiring,
and the `joint_unsat` macro consumed by downstream proof materialization.

DO NOT MODIFY -- benchmark infrastructure.
-/

structure RepoImpl where
  arithmeticV2 : ArithmeticV2Bundle

def canonical : RepoImpl where
  arithmeticV2 := {
    CheckedU128_new := ArithmeticV2.CheckedU128_new
    CheckedU16_new := ArithmeticV2.CheckedU16_new
    CheckedU32_new := ArithmeticV2.CheckedU32_new
    CheckedU64_new := ArithmeticV2.CheckedU64_new
    CheckedU8_new := ArithmeticV2.CheckedU8_new
    CheckedUsize_new := ArithmeticV2.CheckedUsize_new
    CheckedU128_new_overflowed := ArithmeticV2.CheckedU128_new_overflowed
    CheckedU16_new_overflowed := ArithmeticV2.CheckedU16_new_overflowed
    CheckedU32_new_overflowed := ArithmeticV2.CheckedU32_new_overflowed
    CheckedU64_new_overflowed := ArithmeticV2.CheckedU64_new_overflowed
    CheckedU8_new_overflowed := ArithmeticV2.CheckedU8_new_overflowed
    CheckedUsize_new_overflowed := ArithmeticV2.CheckedUsize_new_overflowed
    CheckedU128_is_overflowed := ArithmeticV2.CheckedU128_is_overflowed
    CheckedU16_is_overflowed := ArithmeticV2.CheckedU16_is_overflowed
    CheckedU32_is_overflowed := ArithmeticV2.CheckedU32_is_overflowed
    CheckedU64_is_overflowed := ArithmeticV2.CheckedU64_is_overflowed
    CheckedU8_is_overflowed := ArithmeticV2.CheckedU8_is_overflowed
    CheckedUsize_is_overflowed := ArithmeticV2.CheckedUsize_is_overflowed
    CheckedU128_unwrap := ArithmeticV2.CheckedU128_unwrap
    CheckedU16_unwrap := ArithmeticV2.CheckedU16_unwrap
    CheckedU32_unwrap := ArithmeticV2.CheckedU32_unwrap
    CheckedU64_unwrap := ArithmeticV2.CheckedU64_unwrap
    CheckedU8_unwrap := ArithmeticV2.CheckedU8_unwrap
    CheckedUsize_unwrap := ArithmeticV2.CheckedUsize_unwrap
    CheckedU128_to_option := ArithmeticV2.CheckedU128_to_option
    CheckedU16_to_option := ArithmeticV2.CheckedU16_to_option
    CheckedU32_to_option := ArithmeticV2.CheckedU32_to_option
    CheckedU64_to_option := ArithmeticV2.CheckedU64_to_option
    CheckedU8_to_option := ArithmeticV2.CheckedU8_to_option
    CheckedUsize_to_option := ArithmeticV2.CheckedUsize_to_option
    CheckedU128_add_value := ArithmeticV2.CheckedU128_add_value
    CheckedU16_add_value := ArithmeticV2.CheckedU16_add_value
    CheckedU32_add_value := ArithmeticV2.CheckedU32_add_value
    CheckedU64_add_value := ArithmeticV2.CheckedU64_add_value
    CheckedU8_add_value := ArithmeticV2.CheckedU8_add_value
    CheckedUsize_add_value := ArithmeticV2.CheckedUsize_add_value
    CheckedU128_add_checked := ArithmeticV2.CheckedU128_add_checked
    CheckedU16_add_checked := ArithmeticV2.CheckedU16_add_checked
    CheckedU32_add_checked := ArithmeticV2.CheckedU32_add_checked
    CheckedU64_add_checked := ArithmeticV2.CheckedU64_add_checked
    CheckedU8_add_checked := ArithmeticV2.CheckedU8_add_checked
    CheckedUsize_add_checked := ArithmeticV2.CheckedUsize_add_checked
    CheckedU128_mul_value := ArithmeticV2.CheckedU128_mul_value
    CheckedU16_mul_value := ArithmeticV2.CheckedU16_mul_value
    CheckedU32_mul_value := ArithmeticV2.CheckedU32_mul_value
    CheckedU64_mul_value := ArithmeticV2.CheckedU64_mul_value
    CheckedU8_mul_value := ArithmeticV2.CheckedU8_mul_value
    CheckedUsize_mul_value := ArithmeticV2.CheckedUsize_mul_value
    CheckedU128_mul_checked := ArithmeticV2.CheckedU128_mul_checked
    CheckedU16_mul_checked := ArithmeticV2.CheckedU16_mul_checked
    CheckedU32_mul_checked := ArithmeticV2.CheckedU32_mul_checked
    CheckedU64_mul_checked := ArithmeticV2.CheckedU64_mul_checked
    CheckedU8_mul_checked := ArithmeticV2.CheckedU8_mul_checked
    CheckedUsize_mul_checked := ArithmeticV2.CheckedUsize_mul_checked
  }

/--
`joint_unsat spec_A spec_B [spec_C ...] by <proof>` generates a theorem
stating that the listed specs cannot be jointly satisfied by any `RepoImpl`.
-/
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
