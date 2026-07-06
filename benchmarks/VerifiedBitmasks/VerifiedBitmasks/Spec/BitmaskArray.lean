import VerifiedBitmasks.Impl.BitmaskArray
import VerifiedBitmasks.Harness

/-!
# VerifiedBitmasks.Spec.BitmaskArray

Specifications for the `BitmaskArray` API functions. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`, capturing a refinement
condition: the `Array Bool` implementation must agree with the canonical
`bitmask_*` spec helpers from `BitmaskSpec`, composed via the
interpretation `BitmaskArray.I (A : BArr_T) = A.toList`.

Derived from the `ensures` clauses in `src/BitMask/BitmaskArray.i.dfy`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── bArr_cNewZeros ────────────────────────────────────────────────────────────

/-- `bArr_cNewZeros n` produces an all-zeros bitmask of n bits (array version). -/
def spec_bArr_cNewZeros_correct (impl : RepoImpl) : Prop :=
  ∀ (n : UInt64),
    BitmaskArray.I (impl.verifiedBitmasks.bArr_cNewZeros n) = bitmask_new_zeros n.toNat

/-- The number of bits in `bArr_cNewZeros n` equals n. -/
def spec_bArr_cNewZeros_nbits (impl : RepoImpl) : Prop :=
  ∀ (n : UInt64),
    impl.verifiedBitmasks.bArr_nbits (impl.verifiedBitmasks.bArr_cNewZeros n) = n

-- ── bArr_cNewOnes ─────────────────────────────────────────────────────────────

/-- `bArr_cNewOnes n` produces an all-ones bitmask of n bits (array version). -/
def spec_bArr_cNewOnes_correct (impl : RepoImpl) : Prop :=
  ∀ (n : UInt64),
    BitmaskArray.I (impl.verifiedBitmasks.bArr_cNewOnes n) = bitmask_new_ones n.toNat

/-- The number of bits in `bArr_cNewOnes n` equals n. -/
def spec_bArr_cNewOnes_nbits (impl : RepoImpl) : Prop :=
  ∀ (n : UInt64),
    impl.verifiedBitmasks.bArr_nbits (impl.verifiedBitmasks.bArr_cNewOnes n) = n

-- ── bArr_nbits ────────────────────────────────────────────────────────────────

/-- `bArr_nbits` agrees with the canonical `bitmask_nbits` spec helper via `I`
    (for `UInt64`-representable sizes). -/
def spec_bArr_nbits_correct (impl : RepoImpl) : Prop :=
  ∀ (A : BArr_T), A.size < (2 ^ 64 : Nat) →
    (impl.verifiedBitmasks.bArr_nbits A).toNat = bitmask_nbits (BitmaskArray.I A)

-- ── bArr_popcnt ───────────────────────────────────────────────────────────────

/-- `bArr_popcnt` agrees with the canonical `bitmask_popcnt` spec helper via `I`
    (for `UInt64`-representable sizes). -/
def spec_bArr_popcnt_correct (impl : RepoImpl) : Prop :=
  ∀ (A : BArr_T), A.size < (2 ^ 64 : Nat) →
    (impl.verifiedBitmasks.bArr_popcnt A).toNat = bitmask_popcnt (BitmaskArray.I A)

/-- Population count never exceeds the number of bits (for `UInt64`-representable sizes). -/
def spec_bArr_popcnt_bounded (impl : RepoImpl) : Prop :=
  ∀ (A : BArr_T), A.size < (2 ^ 64 : Nat) →
    impl.verifiedBitmasks.bArr_popcnt A ≤ impl.verifiedBitmasks.bArr_nbits A

-- ── bArr_getBit ───────────────────────────────────────────────────────────────

/-- `bArr_getBit` agrees with the canonical `bitmask_get_bit` spec helper via `I`. -/
def spec_bArr_getBit_correct (impl : RepoImpl) : Prop :=
  ∀ (A : BArr_T) (i : UInt64),
    impl.verifiedBitmasks.bArr_getBit A i = bitmask_get_bit (BitmaskArray.I A) i.toNat

-- ── bArr_setBit ───────────────────────────────────────────────────────────────

/-- `bArr_setBit` agrees with the canonical `bitmask_set_bit` spec helper via `I`. -/
def spec_bArr_setBit_correct (impl : RepoImpl) : Prop :=
  ∀ (A : BArr_T) (i : UInt64),
    BitmaskArray.I (impl.verifiedBitmasks.bArr_setBit A i) =
      bitmask_set_bit (BitmaskArray.I A) i.toNat

-- ── bArr_clearBit ─────────────────────────────────────────────────────────────

/-- `bArr_clearBit` agrees with the canonical `bitmask_clear_bit` spec helper via `I`. -/
def spec_bArr_clearBit_correct (impl : RepoImpl) : Prop :=
  ∀ (A : BArr_T) (i : UInt64),
    BitmaskArray.I (impl.verifiedBitmasks.bArr_clearBit A i) =
      bitmask_clear_bit (BitmaskArray.I A) i.toNat

-- ── bArr_toggleBit ────────────────────────────────────────────────────────────

/-- `bArr_toggleBit` agrees with the canonical `bitmask_toggle_bit` spec helper via `I`. -/
def spec_bArr_toggleBit_correct (impl : RepoImpl) : Prop :=
  ∀ (A : BArr_T) (i : UInt64),
    BitmaskArray.I (impl.verifiedBitmasks.bArr_toggleBit A i) =
      bitmask_toggle_bit (BitmaskArray.I A) i.toNat

-- ── bArr_eq ───────────────────────────────────────────────────────────────────

/-- `bArr_eq` agrees with the canonical `bitmask_eq` spec helper via `I`. -/
def spec_bArr_eq_correct (impl : RepoImpl) : Prop :=
  ∀ (A B : BArr_T),
    impl.verifiedBitmasks.bArr_eq A B = bitmask_eq (BitmaskArray.I A) (BitmaskArray.I B)

-- ── bArr_isZeros ─────────────────────────────────────────────────────────────

/-- `bArr_isZeros` returns true iff all bits of the interpretation are false. -/
def spec_bArr_isZeros_correct (impl : RepoImpl) : Prop :=
  ∀ (A : BArr_T),
    impl.verifiedBitmasks.bArr_isZeros A = (BitmaskArray.I A).all (· == false)

-- ── bArr_isOnes ──────────────────────────────────────────────────────────────

/-- `bArr_isOnes` returns true iff all bits of the interpretation are true. -/
def spec_bArr_isOnes_correct (impl : RepoImpl) : Prop :=
  ∀ (A : BArr_T),
    impl.verifiedBitmasks.bArr_isOnes A = (BitmaskArray.I A).all (· == true)

-- ── bArr_and ──────────────────────────────────────────────────────────────────

/-- `bArr_and` agrees with the canonical `bitmask_and` spec helper via `I`. -/
def spec_bArr_and_correct (impl : RepoImpl) : Prop :=
  ∀ (A B : BArr_T),
    BitmaskArray.I (impl.verifiedBitmasks.bArr_and A B) =
      bitmask_and (BitmaskArray.I A) (BitmaskArray.I B)

-- ── bArr_or ───────────────────────────────────────────────────────────────────

/-- `bArr_or` agrees with the canonical `bitmask_or` spec helper via `I`. -/
def spec_bArr_or_correct (impl : RepoImpl) : Prop :=
  ∀ (A B : BArr_T),
    BitmaskArray.I (impl.verifiedBitmasks.bArr_or A B) =
      bitmask_or (BitmaskArray.I A) (BitmaskArray.I B)

-- ── bArr_xor ──────────────────────────────────────────────────────────────────

/-- `bArr_xor` agrees with the canonical `bitmask_xor` spec helper via `I`. -/
def spec_bArr_xor_correct (impl : RepoImpl) : Prop :=
  ∀ (A B : BArr_T),
    BitmaskArray.I (impl.verifiedBitmasks.bArr_xor A B) =
      bitmask_xor (BitmaskArray.I A) (BitmaskArray.I B)

-- ── bArr_not ──────────────────────────────────────────────────────────────────

/-- `bArr_not` agrees with the canonical `bitmask_not` spec helper via `I`. -/
def spec_bArr_not_correct (impl : RepoImpl) : Prop :=
  ∀ (A : BArr_T),
    BitmaskArray.I (impl.verifiedBitmasks.bArr_not A) = bitmask_not (BitmaskArray.I A)
