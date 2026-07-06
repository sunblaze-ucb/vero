import BitManipulation.Harness
import BitManipulation.Spec.BinaryAndOperator

/-!
# BitManipulation.Spec.BinaryTwosComplement

Specifications for the `twos_complement` API.

DO NOT MODIFY — frozen curator-given content.
-/

/-- The two's complement of zero is `"0b0"`. -/
def spec_tc_zero (impl : RepoImpl) : Prop :=
  impl.bitManipulation.twos_complement 0 = "0b0"

/-- `twos_complement` always returns a well-formed `"0b…"` binary string for any input in the
    library's domain (`n ≤ 0`; the upstream Python raises `ValueError` for positive `n`). -/
def spec_tc_valid_format (impl : RepoImpl) : Prop :=
  ∀ (n : Int), n ≤ 0 →
    spec_helper_isBinaryStr (impl.bitManipulation.twos_complement n) = true

/-- For any negative `n`, the decoded two's complement output satisfies `decoded + (-n) = 2^w`,
    where `w` is the number of bit characters after `"0b"`. -/
def spec_tc_negative_value (impl : RepoImpl) : Prop :=
  ∀ (n : Int), n < 0 →
    let s := impl.bitManipulation.twos_complement n
    let w := (s.toList.drop 2).length
    spec_helper_parseBinary s + (-n) = (2 : Int) ^ w

/-- `twos_complement` returns byte-exactly the upstream Python reference output on the library's
    domain (`n ≤ 0`; the upstream Python raises `ValueError` for positive `n`). -/
def spec_tc_matches_reference (impl : RepoImpl) : Prop :=
  ∀ (n : Int), n ≤ 0 →
    impl.bitManipulation.twos_complement n = BitHelpers.twosComplementString n

/-- For any negative input, the most significant payload bit (first char after `"0b"`) is `'1'`. -/
def spec_tc_negative_high_bit (impl : RepoImpl) : Prop :=
  ∀ (n : Int), n < 0 →
    ((impl.bitManipulation.twos_complement n).toList.drop 2).head? = some '1'

/-- Concrete-value regression points for `twos_complement`. -/
def spec_ground_twos_complement (impl : RepoImpl) : Prop :=
  impl.bitManipulation.twos_complement 0 = "0b0" ∧
  impl.bitManipulation.twos_complement (-1) = "0b11" ∧
  impl.bitManipulation.twos_complement (-5) = "0b1011" ∧
  impl.bitManipulation.twos_complement (-17) = "0b101111"
