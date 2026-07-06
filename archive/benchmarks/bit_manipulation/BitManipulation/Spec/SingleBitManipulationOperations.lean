import BitManipulation.Harness
import BitManipulation.Spec.Aux
import BitManipulation.Spec.BinaryAndOperator
import BitManipulation.Spec.BinaryShifts
import BitManipulation.Spec.BinaryXorOperator

/-!
# BitManipulation.Spec.SingleBitManipulationOperations

Specifications for `set_bit`, `clear_bit`, `flip_bit`, `is_bit_set`, and `get_bit`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- After `set_bit n pos`, `is_bit_set` confirms the bit at `pos` is set. -/
def spec_set_bit_sets (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ pos →
    impl.bitManipulation.is_bit_set (impl.bitManipulation.set_bit n pos) pos = true

/-- After `clear_bit n pos`, `is_bit_set` confirms the bit at `pos` is cleared. -/
def spec_clear_bit_clears (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ pos →
    impl.bitManipulation.is_bit_set (impl.bitManipulation.clear_bit n pos) pos = false

/-- Flipping the same bit twice is an involution: returns the original integer. Guarded by
    `0 ≤ n` to match the sibling single-bit specs — the shared `number.toNat` modeling collapses
    negatives, so the value can only be recovered on non-negative inputs. -/
def spec_flip_bit_involution (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ n → 0 ≤ pos →
    impl.bitManipulation.flip_bit (impl.bitManipulation.flip_bit n pos) pos = n

/-- `is_bit_set n pos` is `true` iff `get_bit n pos` is nonzero. -/
def spec_is_bit_set_get_bit (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ pos →
    impl.bitManipulation.is_bit_set n pos = (impl.bitManipulation.get_bit n pos != 0)

/-- `get_bit n pos` returns either `0` or `1` — it extracts a single bit. -/
def spec_get_bit_binary (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ pos →
    impl.bitManipulation.get_bit n pos = 0 ∨ impl.bitManipulation.get_bit n pos = 1

/-- `set_bit` is idempotent: setting the same bit twice equals setting it once. -/
def spec_set_bit_idempotent (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ pos →
    impl.bitManipulation.set_bit (impl.bitManipulation.set_bit n pos) pos =
      impl.bitManipulation.set_bit n pos

/-- `clear_bit` is idempotent: clearing the same bit twice equals clearing it once. -/
def spec_clear_bit_idempotent (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ pos →
    impl.bitManipulation.clear_bit (impl.bitManipulation.clear_bit n pos) pos =
      impl.bitManipulation.clear_bit n pos

/-- Setting a bit then immediately clearing it equals just clearing it (frame condition). -/
def spec_set_then_clear_neutral (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ pos →
    impl.bitManipulation.clear_bit (impl.bitManipulation.set_bit n pos) pos =
      impl.bitManipulation.clear_bit n pos

/-- `flip_bit n pos` is equivalent to toggling: clear if set, set if clear. -/
def spec_flip_as_toggle (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ pos →
    impl.bitManipulation.flip_bit n pos =
      if impl.bitManipulation.is_bit_set n pos
      then impl.bitManipulation.clear_bit n pos
      else impl.bitManipulation.set_bit n pos

/-- `set_bit` matches the upstream Python reference (`Nat.lor` with `2^pos`). -/
def spec_set_bit_matches_reference (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ n → 0 ≤ pos →
    impl.bitManipulation.set_bit n pos = BitHelpers.setBitValue n pos

/-- `clear_bit` matches the upstream Python reference. -/
def spec_clear_bit_matches_reference (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ n → 0 ≤ pos →
    impl.bitManipulation.clear_bit n pos = BitHelpers.clearBitValue n pos

/-- `flip_bit` matches the upstream Python reference (`Nat.xor` with `2^pos`). -/
def spec_flip_bit_matches_reference (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ n → 0 ≤ pos →
    impl.bitManipulation.flip_bit n pos = BitHelpers.flipBitValue n pos

/-- `is_bit_set` matches the upstream Python reference. -/
def spec_is_bit_set_matches_reference (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ n → 0 ≤ pos →
    impl.bitManipulation.is_bit_set n pos = BitHelpers.isBitSetValue n pos

/-- `get_bit` matches the upstream Python reference (`1` iff `is_bit_set`). -/
def spec_get_bit_matches_reference (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ n → 0 ≤ pos →
    impl.bitManipulation.get_bit n pos = BitHelpers.getBitValue n pos

/-- Clear-then-set is the same as a fresh set: `set_bit (clear_bit n pos) pos = set_bit n pos`. -/
def spec_clear_then_set_neutral (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ pos →
    impl.bitManipulation.set_bit (impl.bitManipulation.clear_bit n pos) pos =
      impl.bitManipulation.set_bit n pos

/-- `flip_bit n pos` is `n XOR 2^pos` at the integer level. -/
def spec_flip_is_xor_with_mask (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ n → 0 ≤ pos →
    impl.bitManipulation.flip_bit n pos =
      ((Nat.xor n.toNat (2 ^ pos.toNat) : Nat) : Int)

/-- After `set_bit`, the bit at `pos` reads as `1` (numeric) and `true` (predicate). -/
def spec_get_after_set (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ pos →
    impl.bitManipulation.get_bit (impl.bitManipulation.set_bit n pos) pos = 1 ∧
    impl.bitManipulation.is_bit_set (impl.bitManipulation.set_bit n pos) pos = true

/-- After `clear_bit`, the bit at `pos` reads as `0` (numeric) and `false` (predicate). -/
def spec_get_after_clear (impl : RepoImpl) : Prop :=
  ∀ (n pos : Int), 0 ≤ pos →
    impl.bitManipulation.get_bit (impl.bitManipulation.clear_bit n pos) pos = 0 ∧
    impl.bitManipulation.is_bit_set (impl.bitManipulation.clear_bit n pos) pos = false

/-- Bit-locality: `set_bit`, `clear_bit`, `flip_bit` at `p` leave the bit at any other
    position `q ≠ p` untouched. -/
def spec_bit_operation_non_interference (impl : RepoImpl) : Prop :=
  ∀ (n p q : Int), 0 ≤ p → 0 ≤ q → p ≠ q →
    impl.bitManipulation.get_bit (impl.bitManipulation.set_bit n p) q =
      impl.bitManipulation.get_bit n q ∧
    impl.bitManipulation.get_bit (impl.bitManipulation.clear_bit n p) q =
      impl.bitManipulation.get_bit n q ∧
    impl.bitManipulation.get_bit (impl.bitManipulation.flip_bit n p) q =
      impl.bitManipulation.get_bit n q

/-- Direct mask/arithmetic characterizations of the single-bit APIs:
    `set_bit n p = n ∨ 2^p`,
    `clear_bit n p = n ∧ ¬2^p` (encoded as `n - (n ∧ 2^p)`),
    `get_bit n p = (n / 2^p) % 2`. -/
def spec_single_bit_agrees_with_arithmetic (impl : RepoImpl) : Prop :=
  ∀ (n p : Int), 0 ≤ n → 0 ≤ p →
    impl.bitManipulation.set_bit n p = ((Nat.lor n.toNat (2 ^ p.toNat) : Nat) : Int) ∧
    impl.bitManipulation.clear_bit n p =
      ((n.toNat - Nat.land n.toNat (2 ^ p.toNat) : Nat) : Int) ∧
    impl.bitManipulation.get_bit n p = (((n.toNat / 2 ^ p.toNat) % 2 : Nat) : Int)

/-- Cross-relation: `(n >> p) AND 1 = get_bit n p` at the decoded-integer level. -/
def spec_shift_and_mask_extracts_bit (impl : RepoImpl) : Prop :=
  ∀ (n p : Int), 0 ≤ n → 0 ≤ p →
    spec_helper_parseBinary
        (impl.bitManipulation.binary_and
          (spec_helper_parseBinary (impl.bitManipulation.logical_right_shift n p)) 1) =
      impl.bitManipulation.get_bit n p

/-- Cross-relation: XOR with `2^p` equals `flip_bit n p` at the decoded-integer level. -/
def spec_xor_equals_flip (impl : RepoImpl) : Prop :=
  ∀ (n p : Int), 0 ≤ n → 0 ≤ p →
    spec_helper_parseBinary (impl.bitManipulation.binary_xor n ((2 ^ p.toNat : Nat) : Int)) =
      impl.bitManipulation.flip_bit n p

/-- Concrete-value regression points across set/clear/flip/get/is_bit_set. -/
def spec_ground_single_bit (impl : RepoImpl) : Prop :=
  impl.bitManipulation.set_bit 0b1101 1 = 15 ∧
  impl.bitManipulation.set_bit 0 5 = 32 ∧
  impl.bitManipulation.clear_bit 0b10010 1 = 16 ∧
  impl.bitManipulation.flip_bit 0b101 1 = 7 ∧
  impl.bitManipulation.flip_bit 0b101 0 = 4 ∧
  impl.bitManipulation.get_bit 0b1010 1 = 1 ∧
  impl.bitManipulation.get_bit 0b1010 0 = 0 ∧
  impl.bitManipulation.is_bit_set 0b1010 3 = true ∧
  impl.bitManipulation.is_bit_set 0b1010 0 = false
