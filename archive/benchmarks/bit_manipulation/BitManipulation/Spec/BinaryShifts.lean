import BitManipulation.Harness
import BitManipulation.Spec.BinaryAndOperator

/-!
# BitManipulation.Spec.BinaryShifts

Specifications for `logical_left_shift`, `logical_right_shift`, and
`arithmetic_right_shift`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- Logical left shift of `n` by `k` positions multiplies the decoded value by `2^k`. -/
def spec_lls_value (impl : RepoImpl) : Prop :=
  ∀ (n k : Int), 0 ≤ n → 0 ≤ k →
    spec_helper_parseBinary (impl.bitManipulation.logical_left_shift n k) =
      n * (2 ^ k.toNat)

/-- Logical right shift of non-negative `n` by `k` is integer floor-division by `2^k`. -/
def spec_lrs_value (impl : RepoImpl) : Prop :=
  ∀ (n k : Int), 0 ≤ n → 0 ≤ k →
    spec_helper_parseBinary (impl.bitManipulation.logical_right_shift n k) =
      n / (2 ^ k.toNat)

/-- For non-negative `n`, arithmetic right shift and logical right shift compute the same value. -/
def spec_ars_nonneg_matches_lrs (impl : RepoImpl) : Prop :=
  ∀ (n k : Int), 0 ≤ n → 0 ≤ k →
    spec_helper_parseBinary (impl.bitManipulation.arithmetic_right_shift n k) =
    spec_helper_parseBinary (impl.bitManipulation.logical_right_shift n k)

/-- `arithmetic_right_shift` always returns a well-formed `"0b…"` string for all integer inputs. -/
def spec_ars_valid_format (impl : RepoImpl) : Prop :=
  ∀ (n k : Int), 0 ≤ k →
    spec_helper_isBinaryStr (impl.bitManipulation.arithmetic_right_shift n k) = true

/-- `logical_left_shift` returns byte-exactly the upstream Python reference output. -/
def spec_lls_matches_reference (impl : RepoImpl) : Prop :=
  ∀ (n k : Int), 0 ≤ n → 0 ≤ k →
    impl.bitManipulation.logical_left_shift n k = BitHelpers.logicalLeftShiftString n k

/-- `logical_right_shift` returns byte-exactly the upstream Python reference output. -/
def spec_lrs_matches_reference (impl : RepoImpl) : Prop :=
  ∀ (n k : Int), 0 ≤ n → 0 ≤ k →
    impl.bitManipulation.logical_right_shift n k = BitHelpers.logicalRightShiftString n k

/-- `arithmetic_right_shift` returns byte-exactly the upstream Python reference output (incl. negative `n`). -/
def spec_ars_matches_reference (impl : RepoImpl) : Prop :=
  ∀ (n k : Int), 0 ≤ k →
    impl.bitManipulation.arithmetic_right_shift n k = BitHelpers.arithmeticRightShiftString n k

/-- `logical_left_shift` always returns a well-formed `"0b…"` literal for non-negative inputs. -/
def spec_lls_valid_format (impl : RepoImpl) : Prop :=
  ∀ (n k : Int), 0 ≤ n → 0 ≤ k →
    spec_helper_isBinaryStr (impl.bitManipulation.logical_left_shift n k) = true

/-- `logical_right_shift` always returns a well-formed `"0b…"` literal for non-negative inputs. -/
def spec_lrs_valid_format (impl : RepoImpl) : Prop :=
  ∀ (n k : Int), 0 ≤ n → 0 ≤ k →
    spec_helper_isBinaryStr (impl.bitManipulation.logical_right_shift n k) = true

/-- Round-trip: `logical_right_shift (logical_left_shift n k) k` recovers `n` (decoded). -/
def spec_left_right_shift_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (n k : Int), 0 ≤ n → 0 ≤ k →
    spec_helper_parseBinary
        (impl.bitManipulation.logical_right_shift
          (spec_helper_parseBinary (impl.bitManipulation.logical_left_shift n k)) k) = n

/-- Shifting by 0 is the identity (decoded values agree with `n`). -/
def spec_shift_zero_identity (impl : RepoImpl) : Prop :=
  ∀ (n : Int), 0 ≤ n →
    spec_helper_parseBinary (impl.bitManipulation.logical_left_shift n 0) = n ∧
    spec_helper_parseBinary (impl.bitManipulation.logical_right_shift n 0) = n

/-- Shift composition: shifting by `s1` then `s2` agrees with shifting by `s1 + s2`
    (decoded values), for both logical shifts. -/
def spec_shift_composition (impl : RepoImpl) : Prop :=
  ∀ (n s1 s2 : Int), 0 ≤ n → 0 ≤ s1 → 0 ≤ s2 →
    (spec_helper_parseBinary
        (impl.bitManipulation.logical_left_shift
          (spec_helper_parseBinary (impl.bitManipulation.logical_left_shift n s1)) s2)
      = spec_helper_parseBinary (impl.bitManipulation.logical_left_shift n (s1 + s2))) ∧
    (spec_helper_parseBinary
        (impl.bitManipulation.logical_right_shift
          (spec_helper_parseBinary (impl.bitManipulation.logical_right_shift n s1)) s2)
      = spec_helper_parseBinary (impl.bitManipulation.logical_right_shift n (s1 + s2)))

/-- Sign-bit preservation for `arithmetic_right_shift`: the first character after `"0b"`
    is `'0'` for non-negative input and `'1'` for negative input. -/
def spec_ars_sign_preservation (impl : RepoImpl) : Prop :=
  (∀ (n k : Int), 0 ≤ n → 0 ≤ k →
    ((impl.bitManipulation.arithmetic_right_shift n k).toList.drop 2).head? = some '0') ∧
  (∀ (n k : Int), n < 0 → 0 ≤ k →
    ((impl.bitManipulation.arithmetic_right_shift n k).toList.drop 2).head? = some '1')

/-- Concrete-value regression points for the shift APIs. -/
def spec_ground_shifts (impl : RepoImpl) : Prop :=
  spec_helper_parseBinary (impl.bitManipulation.logical_left_shift 1 5) = 32 ∧
  spec_helper_parseBinary (impl.bitManipulation.logical_right_shift 17 2) = 4 ∧
  spec_helper_parseBinary (impl.bitManipulation.logical_right_shift 1 5) = 0
