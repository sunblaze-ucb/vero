import ArithmeticV2.Impl.Overflow
import ArithmeticV2.Harness

/-!
# ArithmeticV2.Spec.Overflow

RepoImpl-dependent specifications for checked unsigned overflow arithmetic.
These mirror the source macro method postconditions from `overflow.rs`:
the ghost view tracks exact arithmetic while `v` records whether the
machine-sized value is still representable.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

open ArithmeticV2

def checkedU128Max : Nat := 340282366920938463463374607431768211455
def checkedU16Max : Nat := 65535
def checkedU32Max : Nat := 4294967295
def checkedU64Max : Nat := 18446744073709551615
def checkedU8Max : Nat := 255
def checkedUsizeMax : Nat := 18446744073709551615

/-- CheckedU128.new preserves an in-range input as the checked value view. -/
def spec_CheckedU128_new (impl : RepoImpl) : Prop :=
  ∀ (v : Nat), v ≤ checkedU128Max →
    let r := impl.arithmeticV2.CheckedU128_new v
    CheckedU128_view r = v ∧ r.v = some v ∧ CheckedU128_well_formed r

/-- CheckedU128.new_overflowed records an above-maximum ghost value as overflowed. -/
def spec_CheckedU128_new_overflowed (impl : RepoImpl) : Prop :=
  ∀ (i : Int), (checkedU128Max : Int) < i →
    let r := impl.arithmeticV2.CheckedU128_new_overflowed i
    CheckedU128_view r = i.toNat ∧ r.v = none ∧ CheckedU128_well_formed r

/-- CheckedU128.is_overflowed agrees with the source overflow predicate on well-formed values. -/
def spec_CheckedU128_is_overflowed (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU128), CheckedU128_well_formed x →
    impl.arithmeticV2.CheckedU128_is_overflowed x = CheckedU128_spec_is_overflowed x

/-- CheckedU128.unwrap returns the ghost view when the value is not overflowed. -/
def spec_CheckedU128_unwrap (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU128), CheckedU128_well_formed x → CheckedU128_spec_is_overflowed x = false →
    impl.arithmeticV2.CheckedU128_unwrap x = CheckedU128_view x

/-- CheckedU128.to_option exposes the concrete value exactly when the ghost view fits. -/
def spec_CheckedU128_to_option (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU128), CheckedU128_well_formed x →
    match impl.arithmeticV2.CheckedU128_to_option x with
    | some v => CheckedU128_view x = v ∧ v ≤ checkedU128Max
    | none => checkedU128Max < CheckedU128_view x

/-- CheckedU128.add_value preserves exact ghost addition and output well-formedness. -/
def spec_CheckedU128_add_value (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU128) (v2 : Nat), CheckedU128_well_formed x → v2 ≤ checkedU128Max →
    let r := impl.arithmeticV2.CheckedU128_add_value x v2
    CheckedU128_view r = CheckedU128_view x + v2 ∧ CheckedU128_well_formed r

/-- CheckedU128.add_checked preserves exact ghost addition and output well-formedness. -/
def spec_CheckedU128_add_checked (impl : RepoImpl) : Prop :=
  ∀ (x y : CheckedU128), CheckedU128_well_formed x → CheckedU128_well_formed y →
    let r := impl.arithmeticV2.CheckedU128_add_checked x y
    CheckedU128_view r = CheckedU128_view x + CheckedU128_view y ∧ CheckedU128_well_formed r

/-- CheckedU128.mul_value preserves exact ghost multiplication and output well-formedness. -/
def spec_CheckedU128_mul_value (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU128) (v2 : Nat), CheckedU128_well_formed x → v2 ≤ checkedU128Max →
    let r := impl.arithmeticV2.CheckedU128_mul_value x v2
    CheckedU128_view r = CheckedU128_view x * v2 ∧ CheckedU128_well_formed r

/-- CheckedU128.mul_checked preserves exact ghost multiplication and output well-formedness. -/
def spec_CheckedU128_mul_checked (impl : RepoImpl) : Prop :=
  ∀ (x y : CheckedU128), CheckedU128_well_formed x → CheckedU128_well_formed y →
    let r := impl.arithmeticV2.CheckedU128_mul_checked x y
    CheckedU128_view r = CheckedU128_view x * CheckedU128_view y ∧ CheckedU128_well_formed r

/-- CheckedU16.new preserves an in-range input as the checked value view. -/
def spec_CheckedU16_new (impl : RepoImpl) : Prop :=
  ∀ (v : Nat), v ≤ checkedU16Max →
    let r := impl.arithmeticV2.CheckedU16_new v
    CheckedU16_view r = v ∧ r.v = some v ∧ CheckedU16_well_formed r

/-- CheckedU16.new_overflowed records an above-maximum ghost value as overflowed. -/
def spec_CheckedU16_new_overflowed (impl : RepoImpl) : Prop :=
  ∀ (i : Int), (checkedU16Max : Int) < i →
    let r := impl.arithmeticV2.CheckedU16_new_overflowed i
    CheckedU16_view r = i.toNat ∧ r.v = none ∧ CheckedU16_well_formed r

/-- CheckedU16.is_overflowed agrees with the source overflow predicate on well-formed values. -/
def spec_CheckedU16_is_overflowed (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU16), CheckedU16_well_formed x →
    impl.arithmeticV2.CheckedU16_is_overflowed x = CheckedU16_spec_is_overflowed x

/-- CheckedU16.unwrap returns the ghost view when the value is not overflowed. -/
def spec_CheckedU16_unwrap (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU16), CheckedU16_well_formed x → CheckedU16_spec_is_overflowed x = false →
    impl.arithmeticV2.CheckedU16_unwrap x = CheckedU16_view x

/-- CheckedU16.to_option exposes the concrete value exactly when the ghost view fits. -/
def spec_CheckedU16_to_option (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU16), CheckedU16_well_formed x →
    match impl.arithmeticV2.CheckedU16_to_option x with
    | some v => CheckedU16_view x = v ∧ v ≤ checkedU16Max
    | none => checkedU16Max < CheckedU16_view x

/-- CheckedU16.add_value preserves exact ghost addition and output well-formedness. -/
def spec_CheckedU16_add_value (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU16) (v2 : Nat), CheckedU16_well_formed x → v2 ≤ checkedU16Max →
    let r := impl.arithmeticV2.CheckedU16_add_value x v2
    CheckedU16_view r = CheckedU16_view x + v2 ∧ CheckedU16_well_formed r

/-- CheckedU16.add_checked preserves exact ghost addition and output well-formedness. -/
def spec_CheckedU16_add_checked (impl : RepoImpl) : Prop :=
  ∀ (x y : CheckedU16), CheckedU16_well_formed x → CheckedU16_well_formed y →
    let r := impl.arithmeticV2.CheckedU16_add_checked x y
    CheckedU16_view r = CheckedU16_view x + CheckedU16_view y ∧ CheckedU16_well_formed r

/-- CheckedU16.mul_value preserves exact ghost multiplication and output well-formedness. -/
def spec_CheckedU16_mul_value (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU16) (v2 : Nat), CheckedU16_well_formed x → v2 ≤ checkedU16Max →
    let r := impl.arithmeticV2.CheckedU16_mul_value x v2
    CheckedU16_view r = CheckedU16_view x * v2 ∧ CheckedU16_well_formed r

/-- CheckedU16.mul_checked preserves exact ghost multiplication and output well-formedness. -/
def spec_CheckedU16_mul_checked (impl : RepoImpl) : Prop :=
  ∀ (x y : CheckedU16), CheckedU16_well_formed x → CheckedU16_well_formed y →
    let r := impl.arithmeticV2.CheckedU16_mul_checked x y
    CheckedU16_view r = CheckedU16_view x * CheckedU16_view y ∧ CheckedU16_well_formed r

/-- CheckedU32.new preserves an in-range input as the checked value view. -/
def spec_CheckedU32_new (impl : RepoImpl) : Prop :=
  ∀ (v : Nat), v ≤ checkedU32Max →
    let r := impl.arithmeticV2.CheckedU32_new v
    CheckedU32_view r = v ∧ r.v = some v ∧ CheckedU32_well_formed r

/-- CheckedU32.new_overflowed records an above-maximum ghost value as overflowed. -/
def spec_CheckedU32_new_overflowed (impl : RepoImpl) : Prop :=
  ∀ (i : Int), (checkedU32Max : Int) < i →
    let r := impl.arithmeticV2.CheckedU32_new_overflowed i
    CheckedU32_view r = i.toNat ∧ r.v = none ∧ CheckedU32_well_formed r

/-- CheckedU32.is_overflowed agrees with the source overflow predicate on well-formed values. -/
def spec_CheckedU32_is_overflowed (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU32), CheckedU32_well_formed x →
    impl.arithmeticV2.CheckedU32_is_overflowed x = CheckedU32_spec_is_overflowed x

/-- CheckedU32.unwrap returns the ghost view when the value is not overflowed. -/
def spec_CheckedU32_unwrap (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU32), CheckedU32_well_formed x → CheckedU32_spec_is_overflowed x = false →
    impl.arithmeticV2.CheckedU32_unwrap x = CheckedU32_view x

/-- CheckedU32.to_option exposes the concrete value exactly when the ghost view fits. -/
def spec_CheckedU32_to_option (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU32), CheckedU32_well_formed x →
    match impl.arithmeticV2.CheckedU32_to_option x with
    | some v => CheckedU32_view x = v ∧ v ≤ checkedU32Max
    | none => checkedU32Max < CheckedU32_view x

/-- CheckedU32.add_value preserves exact ghost addition and output well-formedness. -/
def spec_CheckedU32_add_value (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU32) (v2 : Nat), CheckedU32_well_formed x → v2 ≤ checkedU32Max →
    let r := impl.arithmeticV2.CheckedU32_add_value x v2
    CheckedU32_view r = CheckedU32_view x + v2 ∧ CheckedU32_well_formed r

/-- CheckedU32.add_checked preserves exact ghost addition and output well-formedness. -/
def spec_CheckedU32_add_checked (impl : RepoImpl) : Prop :=
  ∀ (x y : CheckedU32), CheckedU32_well_formed x → CheckedU32_well_formed y →
    let r := impl.arithmeticV2.CheckedU32_add_checked x y
    CheckedU32_view r = CheckedU32_view x + CheckedU32_view y ∧ CheckedU32_well_formed r

/-- CheckedU32.mul_value preserves exact ghost multiplication and output well-formedness. -/
def spec_CheckedU32_mul_value (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU32) (v2 : Nat), CheckedU32_well_formed x → v2 ≤ checkedU32Max →
    let r := impl.arithmeticV2.CheckedU32_mul_value x v2
    CheckedU32_view r = CheckedU32_view x * v2 ∧ CheckedU32_well_formed r

/-- CheckedU32.mul_checked preserves exact ghost multiplication and output well-formedness. -/
def spec_CheckedU32_mul_checked (impl : RepoImpl) : Prop :=
  ∀ (x y : CheckedU32), CheckedU32_well_formed x → CheckedU32_well_formed y →
    let r := impl.arithmeticV2.CheckedU32_mul_checked x y
    CheckedU32_view r = CheckedU32_view x * CheckedU32_view y ∧ CheckedU32_well_formed r

/-- CheckedU64.new preserves an in-range input as the checked value view. -/
def spec_CheckedU64_new (impl : RepoImpl) : Prop :=
  ∀ (v : Nat), v ≤ checkedU64Max →
    let r := impl.arithmeticV2.CheckedU64_new v
    CheckedU64_view r = v ∧ r.v = some v ∧ CheckedU64_well_formed r

/-- CheckedU64.new_overflowed records an above-maximum ghost value as overflowed. -/
def spec_CheckedU64_new_overflowed (impl : RepoImpl) : Prop :=
  ∀ (i : Int), (checkedU64Max : Int) < i →
    let r := impl.arithmeticV2.CheckedU64_new_overflowed i
    CheckedU64_view r = i.toNat ∧ r.v = none ∧ CheckedU64_well_formed r

/-- CheckedU64.is_overflowed agrees with the source overflow predicate on well-formed values. -/
def spec_CheckedU64_is_overflowed (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU64), CheckedU64_well_formed x →
    impl.arithmeticV2.CheckedU64_is_overflowed x = CheckedU64_spec_is_overflowed x

/-- CheckedU64.unwrap returns the ghost view when the value is not overflowed. -/
def spec_CheckedU64_unwrap (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU64), CheckedU64_well_formed x → CheckedU64_spec_is_overflowed x = false →
    impl.arithmeticV2.CheckedU64_unwrap x = CheckedU64_view x

/-- CheckedU64.to_option exposes the concrete value exactly when the ghost view fits. -/
def spec_CheckedU64_to_option (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU64), CheckedU64_well_formed x →
    match impl.arithmeticV2.CheckedU64_to_option x with
    | some v => CheckedU64_view x = v ∧ v ≤ checkedU64Max
    | none => checkedU64Max < CheckedU64_view x

/-- CheckedU64.add_value preserves exact ghost addition and output well-formedness. -/
def spec_CheckedU64_add_value (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU64) (v2 : Nat), CheckedU64_well_formed x → v2 ≤ checkedU64Max →
    let r := impl.arithmeticV2.CheckedU64_add_value x v2
    CheckedU64_view r = CheckedU64_view x + v2 ∧ CheckedU64_well_formed r

/-- CheckedU64.add_checked preserves exact ghost addition and output well-formedness. -/
def spec_CheckedU64_add_checked (impl : RepoImpl) : Prop :=
  ∀ (x y : CheckedU64), CheckedU64_well_formed x → CheckedU64_well_formed y →
    let r := impl.arithmeticV2.CheckedU64_add_checked x y
    CheckedU64_view r = CheckedU64_view x + CheckedU64_view y ∧ CheckedU64_well_formed r

/-- CheckedU64.mul_value preserves exact ghost multiplication and output well-formedness. -/
def spec_CheckedU64_mul_value (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU64) (v2 : Nat), CheckedU64_well_formed x → v2 ≤ checkedU64Max →
    let r := impl.arithmeticV2.CheckedU64_mul_value x v2
    CheckedU64_view r = CheckedU64_view x * v2 ∧ CheckedU64_well_formed r

/-- CheckedU64.mul_checked preserves exact ghost multiplication and output well-formedness. -/
def spec_CheckedU64_mul_checked (impl : RepoImpl) : Prop :=
  ∀ (x y : CheckedU64), CheckedU64_well_formed x → CheckedU64_well_formed y →
    let r := impl.arithmeticV2.CheckedU64_mul_checked x y
    CheckedU64_view r = CheckedU64_view x * CheckedU64_view y ∧ CheckedU64_well_formed r

/-- CheckedU8.new preserves an in-range input as the checked value view. -/
def spec_CheckedU8_new (impl : RepoImpl) : Prop :=
  ∀ (v : Nat), v ≤ checkedU8Max →
    let r := impl.arithmeticV2.CheckedU8_new v
    CheckedU8_view r = v ∧ r.v = some v ∧ CheckedU8_well_formed r

/-- CheckedU8.new_overflowed records an above-maximum ghost value as overflowed. -/
def spec_CheckedU8_new_overflowed (impl : RepoImpl) : Prop :=
  ∀ (i : Int), (checkedU8Max : Int) < i →
    let r := impl.arithmeticV2.CheckedU8_new_overflowed i
    CheckedU8_view r = i.toNat ∧ r.v = none ∧ CheckedU8_well_formed r

/-- CheckedU8.is_overflowed agrees with the source overflow predicate on well-formed values. -/
def spec_CheckedU8_is_overflowed (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU8), CheckedU8_well_formed x →
    impl.arithmeticV2.CheckedU8_is_overflowed x = CheckedU8_spec_is_overflowed x

/-- CheckedU8.unwrap returns the ghost view when the value is not overflowed. -/
def spec_CheckedU8_unwrap (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU8), CheckedU8_well_formed x → CheckedU8_spec_is_overflowed x = false →
    impl.arithmeticV2.CheckedU8_unwrap x = CheckedU8_view x

/-- CheckedU8.to_option exposes the concrete value exactly when the ghost view fits. -/
def spec_CheckedU8_to_option (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU8), CheckedU8_well_formed x →
    match impl.arithmeticV2.CheckedU8_to_option x with
    | some v => CheckedU8_view x = v ∧ v ≤ checkedU8Max
    | none => checkedU8Max < CheckedU8_view x

/-- CheckedU8.add_value preserves exact ghost addition and output well-formedness. -/
def spec_CheckedU8_add_value (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU8) (v2 : Nat), CheckedU8_well_formed x → v2 ≤ checkedU8Max →
    let r := impl.arithmeticV2.CheckedU8_add_value x v2
    CheckedU8_view r = CheckedU8_view x + v2 ∧ CheckedU8_well_formed r

/-- CheckedU8.add_checked preserves exact ghost addition and output well-formedness. -/
def spec_CheckedU8_add_checked (impl : RepoImpl) : Prop :=
  ∀ (x y : CheckedU8), CheckedU8_well_formed x → CheckedU8_well_formed y →
    let r := impl.arithmeticV2.CheckedU8_add_checked x y
    CheckedU8_view r = CheckedU8_view x + CheckedU8_view y ∧ CheckedU8_well_formed r

/-- CheckedU8.mul_value preserves exact ghost multiplication and output well-formedness. -/
def spec_CheckedU8_mul_value (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedU8) (v2 : Nat), CheckedU8_well_formed x → v2 ≤ checkedU8Max →
    let r := impl.arithmeticV2.CheckedU8_mul_value x v2
    CheckedU8_view r = CheckedU8_view x * v2 ∧ CheckedU8_well_formed r

/-- CheckedU8.mul_checked preserves exact ghost multiplication and output well-formedness. -/
def spec_CheckedU8_mul_checked (impl : RepoImpl) : Prop :=
  ∀ (x y : CheckedU8), CheckedU8_well_formed x → CheckedU8_well_formed y →
    let r := impl.arithmeticV2.CheckedU8_mul_checked x y
    CheckedU8_view r = CheckedU8_view x * CheckedU8_view y ∧ CheckedU8_well_formed r

/-- CheckedUsize.new preserves an in-range input as the checked value view. -/
def spec_CheckedUsize_new (impl : RepoImpl) : Prop :=
  ∀ (v : Nat), v ≤ checkedUsizeMax →
    let r := impl.arithmeticV2.CheckedUsize_new v
    CheckedUsize_view r = v ∧ r.v = some v ∧ CheckedUsize_well_formed r

/-- CheckedUsize.new_overflowed records an above-maximum ghost value as overflowed. -/
def spec_CheckedUsize_new_overflowed (impl : RepoImpl) : Prop :=
  ∀ (i : Int), (checkedUsizeMax : Int) < i →
    let r := impl.arithmeticV2.CheckedUsize_new_overflowed i
    CheckedUsize_view r = i.toNat ∧ r.v = none ∧ CheckedUsize_well_formed r

/-- CheckedUsize.is_overflowed agrees with the source overflow predicate on well-formed values. -/
def spec_CheckedUsize_is_overflowed (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedUsize), CheckedUsize_well_formed x →
    impl.arithmeticV2.CheckedUsize_is_overflowed x = CheckedUsize_spec_is_overflowed x

/-- CheckedUsize.unwrap returns the ghost view when the value is not overflowed. -/
def spec_CheckedUsize_unwrap (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedUsize), CheckedUsize_well_formed x → CheckedUsize_spec_is_overflowed x = false →
    impl.arithmeticV2.CheckedUsize_unwrap x = CheckedUsize_view x

/-- CheckedUsize.to_option exposes the concrete value exactly when the ghost view fits. -/
def spec_CheckedUsize_to_option (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedUsize), CheckedUsize_well_formed x →
    match impl.arithmeticV2.CheckedUsize_to_option x with
    | some v => CheckedUsize_view x = v ∧ v ≤ checkedUsizeMax
    | none => checkedUsizeMax < CheckedUsize_view x

/-- CheckedUsize.add_value preserves exact ghost addition and output well-formedness. -/
def spec_CheckedUsize_add_value (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedUsize) (v2 : Nat), CheckedUsize_well_formed x → v2 ≤ checkedUsizeMax →
    let r := impl.arithmeticV2.CheckedUsize_add_value x v2
    CheckedUsize_view r = CheckedUsize_view x + v2 ∧ CheckedUsize_well_formed r

/-- CheckedUsize.add_checked preserves exact ghost addition and output well-formedness. -/
def spec_CheckedUsize_add_checked (impl : RepoImpl) : Prop :=
  ∀ (x y : CheckedUsize), CheckedUsize_well_formed x → CheckedUsize_well_formed y →
    let r := impl.arithmeticV2.CheckedUsize_add_checked x y
    CheckedUsize_view r = CheckedUsize_view x + CheckedUsize_view y ∧ CheckedUsize_well_formed r

/-- CheckedUsize.mul_value preserves exact ghost multiplication and output well-formedness. -/
def spec_CheckedUsize_mul_value (impl : RepoImpl) : Prop :=
  ∀ (x : CheckedUsize) (v2 : Nat), CheckedUsize_well_formed x → v2 ≤ checkedUsizeMax →
    let r := impl.arithmeticV2.CheckedUsize_mul_value x v2
    CheckedUsize_view r = CheckedUsize_view x * v2 ∧ CheckedUsize_well_formed r

/-- CheckedUsize.mul_checked preserves exact ghost multiplication and output well-formedness. -/
def spec_CheckedUsize_mul_checked (impl : RepoImpl) : Prop :=
  ∀ (x y : CheckedUsize), CheckedUsize_well_formed x → CheckedUsize_well_formed y →
    let r := impl.arithmeticV2.CheckedUsize_mul_checked x y
    CheckedUsize_view r = CheckedUsize_view x * CheckedUsize_view y ∧ CheckedUsize_well_formed r
