import VerifiedBitmasks.Harness

/-!
# VerifiedBitmasks.Spec.BitmaskImplIF

Specifications for the `BitmaskImplIF` API functions. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`, verifying that each API
function refines the canonical `bitmask_*` spec helper from `BitmaskSpec`.

These specs are derived directly from the `ensures` clauses in
`src/BitMask/Spec/BitmaskImplIF.s.dfy`. Since `T := List Bool` and
`I` is the identity, all refinement conditions reduce to direct equalities
with the `BitmaskSpec` functions.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── bIIF_newZeros ─────────────────────────────────────────────────────────────

/-- `bIIF_newZeros M` produces the canonical all-zeros bitmask of M bits. -/
def spec_bIIF_newZeros_correct (impl : RepoImpl) : Prop :=
  ∀ (M : Nat), impl.verifiedBitmasks.bIIF_newZeros M = bitmask_new_zeros M

/-- The number of bits in `bIIF_newZeros M` equals M. -/
def spec_bIIF_newZeros_nbits (impl : RepoImpl) : Prop :=
  ∀ (M : Nat), impl.verifiedBitmasks.bIIF_nbits (impl.verifiedBitmasks.bIIF_newZeros M) = M

/-- `bIIF_newZeros M` produces an all-zeros bitmask (bIIF_isZeros returns true). -/
def spec_bIIF_newZeros_is_zeros (impl : RepoImpl) : Prop :=
  ∀ (M : Nat), bIIF_isZeros (impl.verifiedBitmasks.bIIF_newZeros M) = true

-- ── bIIF_newOnes ──────────────────────────────────────────────────────────────

/-- `bIIF_newOnes M` produces the canonical all-ones bitmask of M bits. -/
def spec_bIIF_newOnes_correct (impl : RepoImpl) : Prop :=
  ∀ (M : Nat), impl.verifiedBitmasks.bIIF_newOnes M = bitmask_new_ones M

/-- The number of bits in `bIIF_newOnes M` equals M. -/
def spec_bIIF_newOnes_nbits (impl : RepoImpl) : Prop :=
  ∀ (M : Nat), impl.verifiedBitmasks.bIIF_nbits (impl.verifiedBitmasks.bIIF_newOnes M) = M

/-- `bIIF_newOnes M` produces an all-ones bitmask (bIIF_isOnes returns true). -/
def spec_bIIF_newOnes_is_ones (impl : RepoImpl) : Prop :=
  ∀ (M : Nat), bIIF_isOnes (impl.verifiedBitmasks.bIIF_newOnes M) = true

-- ── bIIF_nbits ────────────────────────────────────────────────────────────────

/-- `bIIF_nbits` agrees with the canonical `bitmask_nbits` spec helper. -/
def spec_bIIF_nbits_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T), impl.verifiedBitmasks.bIIF_nbits A = bitmask_nbits A

-- ── bIIF_popcnt ───────────────────────────────────────────────────────────────

/-- `bIIF_popcnt` agrees with the canonical `bitmask_popcnt` spec helper. -/
def spec_bIIF_popcnt_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T), impl.verifiedBitmasks.bIIF_popcnt A = bitmask_popcnt A

/-- Population count never exceeds the number of bits. -/
def spec_bIIF_popcnt_bounded (impl : RepoImpl) : Prop :=
  ∀ (A : T), impl.verifiedBitmasks.bIIF_popcnt A ≤ impl.verifiedBitmasks.bIIF_nbits A

-- ── bIIF_getBit ───────────────────────────────────────────────────────────────

/-- `bIIF_getBit` agrees with the canonical `bitmask_get_bit` spec helper. -/
def spec_bIIF_getBit_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T) (i : Nat), impl.verifiedBitmasks.bIIF_getBit A i = bitmask_get_bit A i

-- ── bIIF_setBit ───────────────────────────────────────────────────────────────

/-- `bIIF_setBit` agrees with the canonical `bitmask_set_bit` spec helper. -/
def spec_bIIF_setBit_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T) (i : Nat), impl.verifiedBitmasks.bIIF_setBit A i = bitmask_set_bit A i

-- ── bIIF_clearBit ─────────────────────────────────────────────────────────────

/-- `bIIF_clearBit` agrees with the canonical `bitmask_clear_bit` spec helper. -/
def spec_bIIF_clearBit_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T) (i : Nat), impl.verifiedBitmasks.bIIF_clearBit A i = bitmask_clear_bit A i

-- ── bIIF_toggleBit ────────────────────────────────────────────────────────────

/-- `bIIF_toggleBit` agrees with the canonical `bitmask_toggle_bit` spec helper. -/
def spec_bIIF_toggleBit_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T) (i : Nat), impl.verifiedBitmasks.bIIF_toggleBit A i = bitmask_toggle_bit A i

-- ── bIIF_and ──────────────────────────────────────────────────────────────────

/-- `bIIF_and` agrees with the canonical `bitmask_and` spec helper. -/
def spec_bIIF_and_correct (impl : RepoImpl) : Prop :=
  ∀ (A B : T), impl.verifiedBitmasks.bIIF_and A B = bitmask_and A B

/-- Pointwise AND preserves the number of bits (for equal-length operands). -/
def spec_bIIF_and_nbits_preserved (impl : RepoImpl) : Prop :=
  ∀ (A B : T), A.length = B.length →
    impl.verifiedBitmasks.bIIF_nbits (impl.verifiedBitmasks.bIIF_and A B) =
      impl.verifiedBitmasks.bIIF_nbits A

-- ── bIIF_or ───────────────────────────────────────────────────────────────────

/-- `bIIF_or` agrees with the canonical `bitmask_or` spec helper. -/
def spec_bIIF_or_correct (impl : RepoImpl) : Prop :=
  ∀ (A B : T), impl.verifiedBitmasks.bIIF_or A B = bitmask_or A B

/-- Pointwise OR preserves the number of bits (for equal-length operands). -/
def spec_bIIF_or_nbits_preserved (impl : RepoImpl) : Prop :=
  ∀ (A B : T), A.length = B.length →
    impl.verifiedBitmasks.bIIF_nbits (impl.verifiedBitmasks.bIIF_or A B) =
      impl.verifiedBitmasks.bIIF_nbits A

-- ── bIIF_xor ──────────────────────────────────────────────────────────────────

/-- `bIIF_xor` agrees with the canonical `bitmask_xor` spec helper. -/
def spec_bIIF_xor_correct (impl : RepoImpl) : Prop :=
  ∀ (A B : T), impl.verifiedBitmasks.bIIF_xor A B = bitmask_xor A B

/-- Pointwise XOR preserves the number of bits (for equal-length operands). -/
def spec_bIIF_xor_nbits_preserved (impl : RepoImpl) : Prop :=
  ∀ (A B : T), A.length = B.length →
    impl.verifiedBitmasks.bIIF_nbits (impl.verifiedBitmasks.bIIF_xor A B) =
      impl.verifiedBitmasks.bIIF_nbits A

-- ── bIIF_not ──────────────────────────────────────────────────────────────────

/-- `bIIF_not` agrees with the canonical `bitmask_not` spec helper. -/
def spec_bIIF_not_correct (impl : RepoImpl) : Prop :=
  ∀ (A : T), impl.verifiedBitmasks.bIIF_not A = bitmask_not A

/-- Pointwise NOT preserves the number of bits. -/
def spec_bIIF_not_nbits_preserved (impl : RepoImpl) : Prop :=
  ∀ (A : T), impl.verifiedBitmasks.bIIF_nbits (impl.verifiedBitmasks.bIIF_not A) =
    impl.verifiedBitmasks.bIIF_nbits A
