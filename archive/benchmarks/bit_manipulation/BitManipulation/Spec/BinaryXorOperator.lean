import BitManipulation.Harness
import BitManipulation.Spec.BinaryAndOperator

/-!
# BitManipulation.Spec.BinaryXorOperator

Specifications for the `binary_xor` API.

DO NOT MODIFY — frozen curator-given content.
-/

/-- The integer decoded from `binary_xor a b` equals the bitwise XOR of `a` and `b`. -/
def spec_xor_value (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    spec_helper_parseBinary (impl.bitManipulation.binary_xor a b) =
      ((a.toNat ^^^ b.toNat : Nat) : Int)

/-- `binary_xor` is commutative: `binary_xor a b = binary_xor b a` as strings. -/
def spec_xor_commutes (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    impl.bitManipulation.binary_xor a b = impl.bitManipulation.binary_xor b a

/-- XOR-ing any non-negative integer with itself yields decoded value 0. -/
def spec_xor_self_zero (impl : RepoImpl) : Prop :=
  ∀ (a : Int), 0 ≤ a →
    spec_helper_parseBinary (impl.bitManipulation.binary_xor a a) = 0

/-- `binary_xor` returns byte-exactly the upstream Python reference output. -/
def spec_xor_matches_reference (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    impl.bitManipulation.binary_xor a b = BitHelpers.binaryXorString a b

/-- `binary_xor` always returns a well-formed `"0b…"` literal for non-negative inputs. -/
def spec_xor_valid_format (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    spec_helper_isBinaryStr (impl.bitManipulation.binary_xor a b) = true

/-- XOR via AND/OR/complement: within the shared bit-width
    `w = max (Nat.log2 a + 1) (Nat.log2 b + 1)`,
    `XOR a b = AND (OR a b) (NOT (AND a b))` at the decoded-integer level. -/
def spec_xor_via_and_or (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    let w := Nat.max (Nat.log2 a.toNat + 1) (Nat.log2 b.toNat + 1)
    let mask : Nat := 2 ^ w - 1
    let or_ab := (spec_helper_parseBinary (impl.bitManipulation.binary_or a b)).toNat
    let and_ab := (spec_helper_parseBinary (impl.bitManipulation.binary_and a b)).toNat
    spec_helper_parseBinary (impl.bitManipulation.binary_xor a b) =
      ((Nat.land or_ab (Nat.xor and_ab mask) : Nat) : Int)

/-- Concrete-value regression points for `binary_xor`. -/
def spec_ground_xor (impl : RepoImpl) : Prop :=
  spec_helper_parseBinary (impl.bitManipulation.binary_xor 256 256) = 0 ∧
  spec_helper_parseBinary (impl.bitManipulation.binary_xor 0 255) = 255 ∧
  spec_helper_parseBinary (impl.bitManipulation.binary_xor 21 30) = 11
