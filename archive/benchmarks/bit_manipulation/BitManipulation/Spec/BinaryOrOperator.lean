import BitManipulation.Harness
import BitManipulation.Spec.BinaryAndOperator

/-!
# BitManipulation.Spec.BinaryOrOperator

Specifications for the `binary_or` API.

DO NOT MODIFY — frozen curator-given content.
-/

/-- `binary_or` always returns a well-formed binary literal `"0b…"` for non-negative inputs. -/
def spec_or_valid_format (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    spec_helper_isBinaryStr (impl.bitManipulation.binary_or a b) = true

/-- The integer decoded from `binary_or a b` equals the bitwise OR of `a` and `b`. -/
def spec_or_value (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    spec_helper_parseBinary (impl.bitManipulation.binary_or a b) =
      ((a.toNat ||| b.toNat : Nat) : Int)

/-- `binary_or` is commutative: `binary_or a b = binary_or b a` as strings. -/
def spec_or_commutes (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    impl.bitManipulation.binary_or a b = impl.bitManipulation.binary_or b a

/-- `binary_or` returns byte-exactly the upstream Python reference output. -/
def spec_or_matches_reference (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), 0 ≤ a → 0 ≤ b →
    impl.bitManipulation.binary_or a b = BitHelpers.binaryOrString a b

/-- Concrete-value regression points for `binary_or`. -/
def spec_ground_or (impl : RepoImpl) : Prop :=
  spec_helper_parseBinary (impl.bitManipulation.binary_or 25 32) = 57 ∧
  spec_helper_parseBinary (impl.bitManipulation.binary_or 0 255) = 255
