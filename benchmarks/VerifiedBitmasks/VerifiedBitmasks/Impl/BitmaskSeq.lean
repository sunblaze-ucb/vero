import VerifiedBitmasks.Impl.BitmaskSpec

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.Impl.BitmaskSeq

Executable sequence-based bitmask implementation. The concrete type `T`
is `List Bool` (reusing the global `BitmaskSpec.T` alias). All API
functions delegate to the canonical `bitmask_*` spec helpers from
`BitmaskSpec` with `UInt64 ↔ Nat` conversions for bit counts and indices.

Translated from `src/BitMask/BitmaskSeq.i.dfy`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies (inside the `!benchmark code` markers).
-/

-- ── Spec helpers (frozen vocabulary, no markers) ──────────────────────────────

namespace BitmaskSeq

/-- Invariant on the sequence bitmask (trivially True for List Bool). -/
def Inv (_A : T) : Prop := True

/-- Interpretation function (identity: List Bool maps to itself). -/
def I (A : T) : T := A

end BitmaskSeq

-- ── API signatures (no markers — fixed vocabulary) ────────────────────────────

namespace VerifiedBitmasks

/-- Signature for `bSeq_cNewZeros`: create an all-zeros bitmask of n bits. -/
abbrev BSeqCNewZerosSig := UInt64 → T

/-- Signature for `bSeq_cNewOnes`: create an all-ones bitmask of n bits. -/
abbrev BSeqCNewOnesSig := UInt64 → T

/-- Signature for `bSeq_nbits`: number of bits as a UInt64. -/
abbrev BSeqNbitsSig := T → UInt64

/-- Signature for `bSeq_popcnt`: count of set bits as a UInt64. -/
abbrev BSeqPopcntSig := T → UInt64

/-- Signature for `bSeq_getBit`: get the value of bit i. -/
abbrev BSeqGetBitSig := T → UInt64 → Bool

/-- Signature for `bSeq_setBit`: return a new bitmask with bit i set to true. -/
abbrev BSeqSetBitSig := T → UInt64 → T

/-- Signature for `bSeq_clearBit`: return a new bitmask with bit i set to false. -/
abbrev BSeqClearBitSig := T → UInt64 → T

/-- Signature for `bSeq_toggleBit`: return a new bitmask with bit i toggled. -/
abbrev BSeqToggleBitSig := T → UInt64 → T

/-- Signature for `bSeq_eq`: boolean equality of two sequence bitmasks. -/
abbrev BSeqEqSig := T → T → Bool

/-- Signature for `bSeq_isZeros`: true iff all bits are false. -/
abbrev BSeqIsZerosSig := T → Bool

/-- Signature for `bSeq_isOnes`: true iff all bits are true. -/
abbrev BSeqIsOnesSig := T → Bool

/-- Signature for `bSeq_and`: pointwise AND of two sequence bitmasks. -/
abbrev BSeqAndSig := T → T → T

/-- Signature for `bSeq_or`: pointwise OR of two sequence bitmasks. -/
abbrev BSeqOrSig := T → T → T

/-- Signature for `bSeq_xor`: pointwise XOR of two sequence bitmasks. -/
abbrev BSeqXorSig := T → T → T

/-- Signature for `bSeq_not`: pointwise NOT of a sequence bitmask. -/
abbrev BSeqNotSig := T → T

end VerifiedBitmasks

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ──────────────────────────────────────────

-- !benchmark @start code_aux def=bSeq_cNewZeros
-- !benchmark @end code_aux def=bSeq_cNewZeros

def VerifiedBitmasks.bSeq_cNewZeros : VerifiedBitmasks.BSeqCNewZerosSig :=
-- !benchmark @start code def=bSeq_cNewZeros
  fun n => bitmask_new_zeros n.toNat
-- !benchmark @end code def=bSeq_cNewZeros

-- !benchmark @start code_aux def=bSeq_cNewOnes
-- !benchmark @end code_aux def=bSeq_cNewOnes

def VerifiedBitmasks.bSeq_cNewOnes : VerifiedBitmasks.BSeqCNewOnesSig :=
-- !benchmark @start code def=bSeq_cNewOnes
  fun n => bitmask_new_ones n.toNat
-- !benchmark @end code def=bSeq_cNewOnes

-- !benchmark @start code_aux def=bSeq_nbits
-- !benchmark @end code_aux def=bSeq_nbits

def VerifiedBitmasks.bSeq_nbits : VerifiedBitmasks.BSeqNbitsSig :=
-- !benchmark @start code def=bSeq_nbits
  fun A => A.length.toUInt64
-- !benchmark @end code def=bSeq_nbits

-- !benchmark @start code_aux def=bSeq_popcnt
-- !benchmark @end code_aux def=bSeq_popcnt

def VerifiedBitmasks.bSeq_popcnt : VerifiedBitmasks.BSeqPopcntSig :=
-- !benchmark @start code def=bSeq_popcnt
  fun A => (A.countP id).toUInt64
-- !benchmark @end code def=bSeq_popcnt

-- !benchmark @start code_aux def=bSeq_getBit
-- !benchmark @end code_aux def=bSeq_getBit

def VerifiedBitmasks.bSeq_getBit : VerifiedBitmasks.BSeqGetBitSig :=
-- !benchmark @start code def=bSeq_getBit
  fun A i => bitmask_get_bit A i.toNat
-- !benchmark @end code def=bSeq_getBit

-- !benchmark @start code_aux def=bSeq_setBit
-- !benchmark @end code_aux def=bSeq_setBit

def VerifiedBitmasks.bSeq_setBit : VerifiedBitmasks.BSeqSetBitSig :=
-- !benchmark @start code def=bSeq_setBit
  fun A i => bitmask_set_bit A i.toNat
-- !benchmark @end code def=bSeq_setBit

-- !benchmark @start code_aux def=bSeq_clearBit
-- !benchmark @end code_aux def=bSeq_clearBit

def VerifiedBitmasks.bSeq_clearBit : VerifiedBitmasks.BSeqClearBitSig :=
-- !benchmark @start code def=bSeq_clearBit
  fun A i => bitmask_clear_bit A i.toNat
-- !benchmark @end code def=bSeq_clearBit

-- !benchmark @start code_aux def=bSeq_toggleBit
-- !benchmark @end code_aux def=bSeq_toggleBit

def VerifiedBitmasks.bSeq_toggleBit : VerifiedBitmasks.BSeqToggleBitSig :=
-- !benchmark @start code def=bSeq_toggleBit
  fun A i => bitmask_toggle_bit A i.toNat
-- !benchmark @end code def=bSeq_toggleBit

-- !benchmark @start code_aux def=bSeq_eq
-- !benchmark @end code_aux def=bSeq_eq

def VerifiedBitmasks.bSeq_eq : VerifiedBitmasks.BSeqEqSig :=
-- !benchmark @start code def=bSeq_eq
  fun A B => bitmask_eq A B
-- !benchmark @end code def=bSeq_eq

-- !benchmark @start code_aux def=bSeq_isZeros
-- !benchmark @end code_aux def=bSeq_isZeros

def VerifiedBitmasks.bSeq_isZeros : VerifiedBitmasks.BSeqIsZerosSig :=
-- !benchmark @start code def=bSeq_isZeros
  fun A => A.all (· == false)
-- !benchmark @end code def=bSeq_isZeros

-- !benchmark @start code_aux def=bSeq_isOnes
-- !benchmark @end code_aux def=bSeq_isOnes

def VerifiedBitmasks.bSeq_isOnes : VerifiedBitmasks.BSeqIsOnesSig :=
-- !benchmark @start code def=bSeq_isOnes
  fun A => A.all (· == true)
-- !benchmark @end code def=bSeq_isOnes

-- !benchmark @start code_aux def=bSeq_and
-- !benchmark @end code_aux def=bSeq_and

def VerifiedBitmasks.bSeq_and : VerifiedBitmasks.BSeqAndSig :=
-- !benchmark @start code def=bSeq_and
  fun A B => bitmask_and A B
-- !benchmark @end code def=bSeq_and

-- !benchmark @start code_aux def=bSeq_or
-- !benchmark @end code_aux def=bSeq_or

def VerifiedBitmasks.bSeq_or : VerifiedBitmasks.BSeqOrSig :=
-- !benchmark @start code def=bSeq_or
  fun A B => bitmask_or A B
-- !benchmark @end code def=bSeq_or

-- !benchmark @start code_aux def=bSeq_xor
-- !benchmark @end code_aux def=bSeq_xor

def VerifiedBitmasks.bSeq_xor : VerifiedBitmasks.BSeqXorSig :=
-- !benchmark @start code def=bSeq_xor
  fun A B => bitmask_xor A B
-- !benchmark @end code def=bSeq_xor

-- !benchmark @start code_aux def=bSeq_not
-- !benchmark @end code_aux def=bSeq_not

def VerifiedBitmasks.bSeq_not : VerifiedBitmasks.BSeqNotSig :=
-- !benchmark @start code def=bSeq_not
  fun A => bitmask_not A
-- !benchmark @end code def=bSeq_not
