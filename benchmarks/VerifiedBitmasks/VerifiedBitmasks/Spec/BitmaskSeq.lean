import VerifiedBitmasks.Harness

/-!
# VerifiedBitmasks.Spec.BitmaskSeq

Specifications for the sequence-based bitmask implementation (`BitmaskSeq`).
Each `spec_*` is a mathematical property over an arbitrary `impl : RepoImpl`
that must hold for any correct implementation of the fifteen `bSeq_*` API
functions.

Specs are derived from the `ensures` clauses in `src/BitMask/BitmaskSeq.i.dfy`.
All properties express that each `bSeq_*` function correctly implements its
corresponding `bitmask_*` spec helper from `BitmaskSpec`, with `UInt64 ↔ Nat`
conversions for bit counts and indices.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── bSeq_cNewZeros ────────────────────────────────────────────────────────────

/-- `bSeq_cNewZeros n` equals the canonical all-zeros bitmask of `n.toNat` bits. -/
def spec_bSeq_cNewZeros_correct (impl : RepoImpl) : Prop :=
  ∀ (n : UInt64), impl.verifiedBitmasks.bSeq_cNewZeros n = bitmask_new_zeros n.toNat

/-- The number of bits in `bSeq_cNewZeros n` equals `n`. -/
def spec_bSeq_cNewZeros_nbits (impl : RepoImpl) : Prop :=
  ∀ (n : UInt64),
    impl.verifiedBitmasks.bSeq_nbits (impl.verifiedBitmasks.bSeq_cNewZeros n) = n

/-- `bSeq_cNewZeros n` is an all-zeros bitmask (`bSeq_isZeros` returns true). -/
def spec_bSeq_cNewZeros_is_zeros (impl : RepoImpl) : Prop :=
  ∀ (n : UInt64),
    impl.verifiedBitmasks.bSeq_isZeros (impl.verifiedBitmasks.bSeq_cNewZeros n) = true

-- ── bSeq_cNewOnes ─────────────────────────────────────────────────────────────

/-- `bSeq_cNewOnes n` equals the canonical all-ones bitmask of `n.toNat` bits. -/
def spec_bSeq_cNewOnes_correct (impl : RepoImpl) : Prop :=
  ∀ (n : UInt64), impl.verifiedBitmasks.bSeq_cNewOnes n = bitmask_new_ones n.toNat

/-- The number of bits in `bSeq_cNewOnes n` equals `n`. -/
def spec_bSeq_cNewOnes_nbits (impl : RepoImpl) : Prop :=
  ∀ (n : UInt64),
    impl.verifiedBitmasks.bSeq_nbits (impl.verifiedBitmasks.bSeq_cNewOnes n) = n

/-- `bSeq_cNewOnes n` is an all-ones bitmask (`bSeq_isOnes` returns true). -/
def spec_bSeq_cNewOnes_is_ones (impl : RepoImpl) : Prop :=
  ∀ (n : UInt64),
    impl.verifiedBitmasks.bSeq_isOnes (impl.verifiedBitmasks.bSeq_cNewOnes n) = true

-- ── bSeq_nbits ────────────────────────────────────────────────────────────────

/-- `bSeq_nbits` agrees with `bitmask_nbits`: returns the list length as UInt64. -/
def spec_bSeq_nbits_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T), impl.verifiedBitmasks.bSeq_nbits A = (bitmask_nbits A).toUInt64

-- ── bSeq_popcnt ───────────────────────────────────────────────────────────────

/-- `bSeq_popcnt` agrees with `bitmask_popcnt`: count of set bits as UInt64. -/
def spec_bSeq_popcnt_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T), impl.verifiedBitmasks.bSeq_popcnt A = (bitmask_popcnt A).toUInt64

/-- Population count never exceeds the number of bits (for `UInt64`-representable lengths). -/
def spec_bSeq_popcnt_bounded (impl : RepoImpl) : Prop :=
  ∀ (A : T), A.length < (2 ^ 64 : Nat) →
    impl.verifiedBitmasks.bSeq_popcnt A ≤ impl.verifiedBitmasks.bSeq_nbits A

-- ── bSeq_getBit ───────────────────────────────────────────────────────────────

/-- `bSeq_getBit A i` agrees with `bitmask_get_bit A i.toNat`. -/
def spec_bSeq_getBit_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T) (i : UInt64),
    impl.verifiedBitmasks.bSeq_getBit A i = bitmask_get_bit A i.toNat

-- ── bSeq_setBit ───────────────────────────────────────────────────────────────

/-- `bSeq_setBit A i` agrees with `bitmask_set_bit A i.toNat`. -/
def spec_bSeq_setBit_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T) (i : UInt64),
    impl.verifiedBitmasks.bSeq_setBit A i = bitmask_set_bit A i.toNat

/-- Setting bit i and then reading it back returns true (within bounds). -/
def spec_bSeq_setBit_get (impl : RepoImpl) : Prop :=
  ∀ (A : T) (i : UInt64), i.toNat < A.length →
    impl.verifiedBitmasks.bSeq_getBit (impl.verifiedBitmasks.bSeq_setBit A i) i = true

-- ── bSeq_clearBit ─────────────────────────────────────────────────────────────

/-- `bSeq_clearBit A i` agrees with `bitmask_clear_bit A i.toNat`. -/
def spec_bSeq_clearBit_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T) (i : UInt64),
    impl.verifiedBitmasks.bSeq_clearBit A i = bitmask_clear_bit A i.toNat

/-- Clearing bit i and then reading it back returns false (within bounds). -/
def spec_bSeq_clearBit_get (impl : RepoImpl) : Prop :=
  ∀ (A : T) (i : UInt64), i.toNat < A.length →
    impl.verifiedBitmasks.bSeq_getBit (impl.verifiedBitmasks.bSeq_clearBit A i) i = false

-- ── bSeq_toggleBit ────────────────────────────────────────────────────────────

/-- `bSeq_toggleBit A i` agrees with `bitmask_toggle_bit A i.toNat`. -/
def spec_bSeq_toggleBit_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T) (i : UInt64),
    impl.verifiedBitmasks.bSeq_toggleBit A i = bitmask_toggle_bit A i.toNat

-- ── bSeq_eq ───────────────────────────────────────────────────────────────────

/-- `bSeq_eq` agrees with `bitmask_eq`: boolean equality of two bitmasks. -/
def spec_bSeq_eq_correct (impl : RepoImpl) : Prop :=
  ∀ (A B : T), impl.verifiedBitmasks.bSeq_eq A B = bitmask_eq A B

/-- `bSeq_eq A A` is always true (reflexivity). -/
def spec_bSeq_eq_refl (impl : RepoImpl) : Prop :=
  ∀ (A : T), impl.verifiedBitmasks.bSeq_eq A A = true

-- ── bSeq_isZeros ──────────────────────────────────────────────────────────────

/-- `bSeq_isZeros A = true` iff every bit is false. -/
def spec_bSeq_isZeros_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T), impl.verifiedBitmasks.bSeq_isZeros A = A.all (· == false)

-- ── bSeq_isOnes ───────────────────────────────────────────────────────────────

/-- `bSeq_isOnes A = true` iff every bit is true. -/
def spec_bSeq_isOnes_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T), impl.verifiedBitmasks.bSeq_isOnes A = A.all (· == true)

-- ── bSeq_and ──────────────────────────────────────────────────────────────────

/-- `bSeq_and A B` agrees with `bitmask_and A B`. -/
def spec_bSeq_and_correct (impl : RepoImpl) : Prop :=
  ∀ (A B : T), impl.verifiedBitmasks.bSeq_and A B = bitmask_and A B

/-- AND preserves the number of bits (length of the shorter operand). -/
def spec_bSeq_and_nbits_preserved (impl : RepoImpl) : Prop :=
  ∀ (A B : T), A.length = B.length →
    impl.verifiedBitmasks.bSeq_nbits (impl.verifiedBitmasks.bSeq_and A B) =
      impl.verifiedBitmasks.bSeq_nbits A

-- ── bSeq_or ───────────────────────────────────────────────────────────────────

/-- `bSeq_or A B` agrees with `bitmask_or A B`. -/
def spec_bSeq_or_correct (impl : RepoImpl) : Prop :=
  ∀ (A B : T), impl.verifiedBitmasks.bSeq_or A B = bitmask_or A B

/-- OR preserves the number of bits (length of the shorter operand). -/
def spec_bSeq_or_nbits_preserved (impl : RepoImpl) : Prop :=
  ∀ (A B : T), A.length = B.length →
    impl.verifiedBitmasks.bSeq_nbits (impl.verifiedBitmasks.bSeq_or A B) =
      impl.verifiedBitmasks.bSeq_nbits A

-- ── bSeq_xor ──────────────────────────────────────────────────────────────────

/-- `bSeq_xor A B` agrees with `bitmask_xor A B`. -/
def spec_bSeq_xor_correct (impl : RepoImpl) : Prop :=
  ∀ (A B : T), impl.verifiedBitmasks.bSeq_xor A B = bitmask_xor A B

/-- XOR preserves the number of bits (length of the shorter operand). -/
def spec_bSeq_xor_nbits_preserved (impl : RepoImpl) : Prop :=
  ∀ (A B : T), A.length = B.length →
    impl.verifiedBitmasks.bSeq_nbits (impl.verifiedBitmasks.bSeq_xor A B) =
      impl.verifiedBitmasks.bSeq_nbits A

-- ── bSeq_not ──────────────────────────────────────────────────────────────────

/-- `bSeq_not A` agrees with `bitmask_not A`. -/
def spec_bSeq_not_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T), impl.verifiedBitmasks.bSeq_not A = bitmask_not A

/-- NOT preserves the number of bits. -/
def spec_bSeq_not_nbits_preserved (impl : RepoImpl) : Prop :=
  ∀ (A : T),
    impl.verifiedBitmasks.bSeq_nbits (impl.verifiedBitmasks.bSeq_not A) =
      impl.verifiedBitmasks.bSeq_nbits A

/-- Double NOT is identity. -/
def spec_bSeq_not_involutive (impl : RepoImpl) : Prop :=
  ∀ (A : T),
    impl.verifiedBitmasks.bSeq_not (impl.verifiedBitmasks.bSeq_not A) = A
