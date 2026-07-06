import VerifiedBitmasks.Harness

/-!
# VerifiedBitmasks.Spec.MachineWords

Specifications for machine-word bitwise operations. Each `spec_*` is a
mathematical property over an arbitrary `impl : RepoImpl`, accessing API
functions via `impl.verifiedBitmasks.<fn>`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── AND specs ────────────────────────────────────────────────────────────────

/-- AND of a with itself yields a (idempotency). -/
def spec_bitwise_and_self (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseAnd a a = a

/-- AND with all-zeros yields all-zeros. -/
def spec_bitwise_and_zero (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseAnd a impl.verifiedBitmasks.bitwiseZeros = impl.verifiedBitmasks.bitwiseZeros

/-- AND with all-ones yields the original value. -/
def spec_bitwise_and_ones (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseAnd a impl.verifiedBitmasks.bitwiseOnes = a

/-- a = b iff (a AND ones) = (b AND ones). -/
def spec_bitwise_and_ones_eq (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64), (a = b) ↔ (impl.verifiedBitmasks.bitwiseAnd a impl.verifiedBitmasks.bitwiseOnes = impl.verifiedBitmasks.bitwiseAnd b impl.verifiedBitmasks.bitwiseOnes)

/-- Bitwise AND is commutative. -/
def spec_bitwise_and_comm (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64), impl.verifiedBitmasks.bitwiseAnd a b = impl.verifiedBitmasks.bitwiseAnd b a

/-- Bitwise AND is associative. -/
def spec_bitwise_and_assoc (impl : RepoImpl) : Prop :=
  ∀ (a b c : UInt64), impl.verifiedBitmasks.bitwiseAnd a (impl.verifiedBitmasks.bitwiseAnd b c) = impl.verifiedBitmasks.bitwiseAnd (impl.verifiedBitmasks.bitwiseAnd a b) c

/-- AND distributes: (a AND b) AND c = (a AND c) AND (b AND c). -/
def spec_bitwise_and_dist (impl : RepoImpl) : Prop :=
  ∀ (a b c : UInt64), impl.verifiedBitmasks.bitwiseAnd (impl.verifiedBitmasks.bitwiseAnd a b) c = impl.verifiedBitmasks.bitwiseAnd (impl.verifiedBitmasks.bitwiseAnd a c) (impl.verifiedBitmasks.bitwiseAnd b c)

/-- AND of COMP(a) with a yields zero. -/
def spec_bitwise_and_comp_self (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseAnd (impl.verifiedBitmasks.bitwiseComp a) a = 0

/-- AND of NOT(a) with a yields zero. -/
def spec_bitwise_and_not_self (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseAnd (impl.verifiedBitmasks.bitwiseNot a) a = 0

/-- AND of two bit-masked values is zero iff at least one is zero. -/
def spec_bitwise_and_bit_dist (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64) (i : UInt64), i < BitFields.WORD_SIZE →
    ((impl.verifiedBitmasks.bitwiseAnd (impl.verifiedBitmasks.bitwiseAnd a (impl.verifiedBitmasks.bitwiseBit i)) (impl.verifiedBitmasks.bitwiseAnd b (impl.verifiedBitmasks.bitwiseBit i)) = 0) ↔
     ((impl.verifiedBitmasks.bitwiseAnd a (impl.verifiedBitmasks.bitwiseBit i) = 0) ∨ (impl.verifiedBitmasks.bitwiseAnd b (impl.verifiedBitmasks.bitwiseBit i) = 0)))

/-- Bit i of (a AND b) equals the conjunction of bit i of a and bit i of b. -/
def spec_bitwise_and_is_intersection (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64) (i : UInt64), i < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseAnd a b) i = (impl.verifiedBitmasks.bitwiseGetBit a i && impl.verifiedBitmasks.bitwiseGetBit b i)

-- ── OR specs ─────────────────────────────────────────────────────────────────

/-- OR of a with itself yields a (idempotency). -/
def spec_bitwise_or_self (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseOr a a = a

/-- OR with zero yields the original value. -/
def spec_bitwise_or_zero (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseOr a 0 = a

/-- OR with all-ones yields all-ones. -/
def spec_bitwise_or_ones (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseOr a impl.verifiedBitmasks.bitwiseOnes = impl.verifiedBitmasks.bitwiseOnes

/-- Bitwise OR is commutative. -/
def spec_bitwise_or_comm (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64), impl.verifiedBitmasks.bitwiseOr a b = impl.verifiedBitmasks.bitwiseOr b a

/-- Bitwise OR is associative. -/
def spec_bitwise_or_assoc (impl : RepoImpl) : Prop :=
  ∀ (a b c : UInt64), impl.verifiedBitmasks.bitwiseOr a (impl.verifiedBitmasks.bitwiseOr b c) = impl.verifiedBitmasks.bitwiseOr (impl.verifiedBitmasks.bitwiseOr a b) c

/-- OR distributes: (a OR b) OR c = (a OR c) OR (b OR c). -/
def spec_bitwise_or_dist (impl : RepoImpl) : Prop :=
  ∀ (a b c : UInt64), impl.verifiedBitmasks.bitwiseOr (impl.verifiedBitmasks.bitwiseOr a b) c = impl.verifiedBitmasks.bitwiseOr (impl.verifiedBitmasks.bitwiseOr a c) (impl.verifiedBitmasks.bitwiseOr b c)

/-- If (a OR b) = 0, then a = 0 and b = 0. -/
def spec_bitwise_or_zero_implies_args (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64), impl.verifiedBitmasks.bitwiseOr a b = 0 → a = 0 ∧ b = 0

/-- Bit i of (a OR b) equals the disjunction of bit i of a and bit i of b. -/
def spec_bitwise_or_is_union (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64) (i : UInt64), i < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseOr a b) i = (impl.verifiedBitmasks.bitwiseGetBit a i || impl.verifiedBitmasks.bitwiseGetBit b i)

-- ── XOR specs ────────────────────────────────────────────────────────────────

/-- XOR of a with itself yields zero. -/
def spec_bitwise_xor_self (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseXor a a = 0

/-- XOR with zero yields the original value. -/
def spec_bitwise_xor_zero (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseXor a 0 = a

/-- XOR with all-ones equals bitwise NOT. -/
def spec_bitwise_xor_ones (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseXor a impl.verifiedBitmasks.bitwiseOnes = impl.verifiedBitmasks.bitwiseNot a

/-- Bitwise XOR is commutative. -/
def spec_bitwise_xor_comm (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64), impl.verifiedBitmasks.bitwiseXor a b = impl.verifiedBitmasks.bitwiseXor b a

/-- Bitwise XOR is associative. -/
def spec_bitwise_xor_assoc (impl : RepoImpl) : Prop :=
  ∀ (a b c : UInt64), impl.verifiedBitmasks.bitwiseXor a (impl.verifiedBitmasks.bitwiseXor b c) = impl.verifiedBitmasks.bitwiseXor (impl.verifiedBitmasks.bitwiseXor a b) c

/-- If (a XOR b) = 0, then a = b. -/
def spec_bitwise_xor_zero_implies_args (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64), impl.verifiedBitmasks.bitwiseXor a b = 0 → a = b

/-- Bit i of (a XOR b) equals the inequality of bit i of a and bit i of b. -/
def spec_bitwise_xor_is_not_eq (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64) (i : UInt64), i < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseXor a b) i = (impl.verifiedBitmasks.bitwiseGetBit a i != impl.verifiedBitmasks.bitwiseGetBit b i)

-- ── NOT / COMP specs ─────────────────────────────────────────────────────────

/-- BitwiseNot and BitwiseComp produce the same result. -/
def spec_bitwise_not_comp_eq (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseNot a = impl.verifiedBitmasks.bitwiseComp a

/-- Double NOT returns the original value (involution). -/
def spec_bitwise_not_not (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseNot (impl.verifiedBitmasks.bitwiseNot a) = a

/-- Double COMP returns the original value (involution). -/
def spec_bitwise_comp_comp (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64), impl.verifiedBitmasks.bitwiseComp (impl.verifiedBitmasks.bitwiseComp a) = a

/-- Bit i of NOT(a) equals the negation of bit i of a. -/
def spec_bitwise_not_is_not (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64) (i : UInt64), i < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseNot a) i = !impl.verifiedBitmasks.bitwiseGetBit a i

/-- NOT of all-ones is all-zeros; NOT of all-zeros is all-ones. -/
def spec_bitwise_not_ones (impl : RepoImpl) : Prop :=
  impl.verifiedBitmasks.bitwiseNot impl.verifiedBitmasks.bitwiseOnes = impl.verifiedBitmasks.bitwiseZeros ∧
  impl.verifiedBitmasks.bitwiseNot impl.verifiedBitmasks.bitwiseZeros = impl.verifiedBitmasks.bitwiseOnes

-- ── BitwiseBit specs ─────────────────────────────────────────────────────────

/-- BitwiseBit(i) is never zero for any valid bit index. -/
def spec_bitwise_bit_not_zero (impl : RepoImpl) : Prop :=
  ∀ (i : UInt64), i < BitFields.WORD_SIZE → impl.verifiedBitmasks.bitwiseBit i ≠ 0

/-- Bit i of BitwiseBit(i) is set. -/
def spec_bitwise_bit_is_set (impl : RepoImpl) : Prop :=
  ∀ (i : UInt64), i < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseBit i) i = true

/-- Bit j of BitwiseBit(i) is not set when i ≠ j. -/
def spec_bitwise_bit_not_set (impl : RepoImpl) : Prop :=
  ∀ (i j : UInt64), i < BitFields.WORD_SIZE → j < BitFields.WORD_SIZE → i ≠ j →
    impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseBit i) j = false

/-- BitwiseBit(i) AND BitwiseBit(j) = 0 when i ≠ j. -/
def spec_bitwise_not_equal_and_zero (impl : RepoImpl) : Prop :=
  ∀ (i j : UInt64), i ≠ j → i < BitFields.WORD_SIZE → j < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseAnd (impl.verifiedBitmasks.bitwiseBit i) (impl.verifiedBitmasks.bitwiseBit j) = 0

-- ── BitwiseOnes / BitwiseZeros specs ─────────────────────────────────────────

/-- Every bit of bitwiseOnes is set. -/
def spec_bitwise_ones_bit_is_set (impl : RepoImpl) : Prop :=
  ∀ (i : UInt64), i < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseGetBit impl.verifiedBitmasks.bitwiseOnes i = true

/-- No bit of bitwiseZeros is set. -/
def spec_bitwise_zeros_not_bit_is_set (impl : RepoImpl) : Prop :=
  ∀ (i : UInt64), i < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseGetBit impl.verifiedBitmasks.bitwiseZeros i = false

-- ── BitwiseMask specs ────────────────────────────────────────────────────────

/-- BitwiseMask(64) equals bitwiseOnes. -/
def spec_bitwise_mask_is_ones (impl : RepoImpl) : Prop :=
  impl.verifiedBitmasks.bitwiseMask 64 = impl.verifiedBitmasks.bitwiseOnes

/-- BitwiseMask(0) equals bitwiseZeros. -/
def spec_bitwise_mask_is_zeros (impl : RepoImpl) : Prop :=
  impl.verifiedBitmasks.bitwiseMask 0 = impl.verifiedBitmasks.bitwiseZeros

/-- BitwiseMask(i+1) = BitwiseMask(i) OR BitwiseBit(i). -/
def spec_bitwise_mask_extend_bit_or (impl : RepoImpl) : Prop :=
  ∀ (i : UInt64), i < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseMask (i + 1) = impl.verifiedBitmasks.bitwiseOr (impl.verifiedBitmasks.bitwiseMask i) (impl.verifiedBitmasks.bitwiseBit i)

/-- BitwiseMask(i) = BitwiseMask(i-1) OR BitwiseBit(i-1) for i > 0. -/
def spec_bitwise_mask_extend_bit_or_less (impl : RepoImpl) : Prop :=
  ∀ (i : UInt64), 0 < i → i ≤ BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseMask i = impl.verifiedBitmasks.bitwiseOr (impl.verifiedBitmasks.bitwiseMask (i - 1)) (impl.verifiedBitmasks.bitwiseBit (i - 1))

/-- BitwiseMask(i+1) = SetBit(BitwiseMask(i), i). -/
def spec_bitwise_mask_extend_bit_set (impl : RepoImpl) : Prop :=
  ∀ (i : UInt64), i < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseMask (i + 1) = impl.verifiedBitmasks.bitwiseSetBit (impl.verifiedBitmasks.bitwiseMask i) i

/-- BitwiseMask(i) = SetBit(BitwiseMask(i-1), i-1) for i > 0. -/
def spec_bitwise_mask_extend_bit_set_less (impl : RepoImpl) : Prop :=
  ∀ (i : UInt64), 0 < i → i ≤ BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseMask i = impl.verifiedBitmasks.bitwiseSetBit (impl.verifiedBitmasks.bitwiseMask (i - 1)) (i - 1)

-- ── SetBit / ClearBit / ToggleBit specs ──────────────────────────────────────

/-- After SetBit(a, i), bit i is set. -/
def spec_bitwise_set_self (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64) (i : UInt64), i < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseSetBit a i) i = true

/-- SetBit(a, i) does not change bit j when i ≠ j. -/
def spec_bitwise_set_other (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64) (i j : UInt64), i < BitFields.WORD_SIZE → j < BitFields.WORD_SIZE → i ≠ j →
    impl.verifiedBitmasks.bitwiseGetBit a j = impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseSetBit a i) j

/-- After ClearBit(a, i), bit i is cleared. -/
def spec_bitwise_clear_self (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64) (i : UInt64), i < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseClearBit a i) i = false

/-- ClearBit(a, i) does not change bit j when i ≠ j. -/
def spec_bitwise_clear_other (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64) (i j : UInt64), i < BitFields.WORD_SIZE → j < BitFields.WORD_SIZE → i ≠ j →
    impl.verifiedBitmasks.bitwiseGetBit a j = impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseClearBit a i) j

/-- SetBit(a, i) does not change any bit j ≠ i. -/
def spec_bitwise_set_not_change_others (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64) (i : UInt64), i < BitFields.WORD_SIZE →
    ∀ (j : UInt64), j < BitFields.WORD_SIZE → i ≠ j →
      impl.verifiedBitmasks.bitwiseGetBit a j = impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseSetBit a i) j

/-- ClearBit(a, i) does not change any bit j ≠ i. -/
def spec_bitwise_clear_not_change_others (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64) (i : UInt64), i < BitFields.WORD_SIZE →
    ∀ (j : UInt64), j < BitFields.WORD_SIZE → i ≠ j →
      impl.verifiedBitmasks.bitwiseGetBit a j = impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseClearBit a i) j

/-- ToggleBit(a, i) does not change any bit j ≠ i. -/
def spec_bitwise_toggle_not_change_others (impl : RepoImpl) : Prop :=
  ∀ (a : UInt64) (i : UInt64), i < BitFields.WORD_SIZE →
    ∀ (j : UInt64), j < BitFields.WORD_SIZE → i ≠ j →
      impl.verifiedBitmasks.bitwiseGetBit a j = impl.verifiedBitmasks.bitwiseGetBit (impl.verifiedBitmasks.bitwiseToggleBit a i) j

-- ── Distribution / DeMorgan specs ────────────────────────────────────────────

/-- AND distributes over OR: (a OR b) AND c = (a AND c) OR (b AND c). -/
def spec_bitwise_and_or_dist (impl : RepoImpl) : Prop :=
  ∀ (a b c : UInt64), impl.verifiedBitmasks.bitwiseAnd (impl.verifiedBitmasks.bitwiseOr a b) c = impl.verifiedBitmasks.bitwiseOr (impl.verifiedBitmasks.bitwiseAnd a c) (impl.verifiedBitmasks.bitwiseAnd b c)

/-- OR distributes over AND: (a AND b) OR c = (a OR c) AND (b OR c). -/
def spec_bitwise_or_and_dist (impl : RepoImpl) : Prop :=
  ∀ (a b c : UInt64), impl.verifiedBitmasks.bitwiseOr (impl.verifiedBitmasks.bitwiseAnd a b) c = impl.verifiedBitmasks.bitwiseAnd (impl.verifiedBitmasks.bitwiseOr a c) (impl.verifiedBitmasks.bitwiseOr b c)

/-- (a OR b) AND b = b (absorption). -/
def spec_bitwise_or_and_self (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64), impl.verifiedBitmasks.bitwiseAnd (impl.verifiedBitmasks.bitwiseOr a b) b = b

/-- DeMorgan: NOT(a OR b) = NOT(a) AND NOT(b). -/
def spec_bitwise_demorgan_not_or (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64), impl.verifiedBitmasks.bitwiseNot (impl.verifiedBitmasks.bitwiseOr a b) = impl.verifiedBitmasks.bitwiseAnd (impl.verifiedBitmasks.bitwiseNot a) (impl.verifiedBitmasks.bitwiseNot b)

/-- DeMorgan: NOT(a AND b) = NOT(a) OR NOT(b). -/
def spec_bitwise_demorgan_not_and (impl : RepoImpl) : Prop :=
  ∀ (a b : UInt64), impl.verifiedBitmasks.bitwiseNot (impl.verifiedBitmasks.bitwiseAnd a b) = impl.verifiedBitmasks.bitwiseOr (impl.verifiedBitmasks.bitwiseNot a) (impl.verifiedBitmasks.bitwiseNot b)

/-- COMP(BitwiseBit(i)) AND BitwiseBit(j) = BitwiseBit(j) when i ≠ j. -/
def spec_bitwise_comp_not_equal (impl : RepoImpl) : Prop :=
  ∀ (i j : UInt64), i ≠ j → i < BitFields.WORD_SIZE → j < BitFields.WORD_SIZE →
    impl.verifiedBitmasks.bitwiseAnd (impl.verifiedBitmasks.bitwiseComp (impl.verifiedBitmasks.bitwiseBit i)) (impl.verifiedBitmasks.bitwiseBit j) = impl.verifiedBitmasks.bitwiseBit j
