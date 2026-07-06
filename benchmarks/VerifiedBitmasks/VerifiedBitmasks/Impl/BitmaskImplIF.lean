import VerifiedBitmasks.Impl.BitmaskSpec

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.Impl.BitmaskImplIF

Bitmask implementation interface (`BitmaskImplIF`) instantiated with
`T := List Bool` (identical to `BitmaskSpec.T`) and identity interpretation
`I`. All concrete API functions delegate to the canonical `bitmask_*` spec
helpers from `BitmaskSpec`, making the invariant `Inv` and `ValidSize`
trivially true.

Translated from `src/BitMask/Spec/BitmaskImplIF.s.dfy`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Spec helpers (frozen vocabulary) ─────────────────────────────────────────

namespace BitmaskImplIF

/-- Invariant on the concrete bitmask type (trivially True for List Bool). -/
def Inv (_A : T) : Prop := True

/-- Predicate that any size is valid (trivially True). -/
def ValidSize (_n : Nat) : Prop := True

/-- Interpretation function from concrete T to abstract T (identity since
    both are `List Bool`). -/
def I (A : T) : T := A

end BitmaskImplIF

/-- Boolean equality for BitmaskImplIF — delegates to `bitmask_eq`. -/
def bIIF_eq (A B : T) : Bool := bitmask_eq A B

/-- True iff all bits of the bitmask are false. -/
def bIIF_isZeros (A : T) : Bool := A.all (· == false)

/-- True iff all bits of the bitmask are true. -/
def bIIF_isOnes (A : T) : Bool := A.all (· == true)

-- ── API signatures (no markers — fixed vocabulary) ─────────────────────────

namespace VerifiedBitmasks

/-- Signature for `bIIF_newZeros`: create an all-zeros bitmask of M bits. -/
abbrev BIIFNewZerosSig := Nat → T

/-- Signature for `bIIF_newOnes`: create an all-ones bitmask of M bits. -/
abbrev BIIFNewOnesSig := Nat → T

/-- Signature for `bIIF_nbits`: number of bits in the bitmask. -/
abbrev BIIFNbitsSig := T → Nat

/-- Signature for `bIIF_popcnt`: count of set (true) bits. -/
abbrev BIIFPopcntSig := T → Nat

/-- Signature for `bIIF_getBit`: get the value of bit i. -/
abbrev BIIFGetBitSig := T → Nat → Bool

/-- Signature for `bIIF_setBit`: set bit i to true. -/
abbrev BIIFSetBitSig := T → Nat → T

/-- Signature for `bIIF_clearBit`: set bit i to false. -/
abbrev BIIFClearBitSig := T → Nat → T

/-- Signature for `bIIF_toggleBit`: toggle bit i. -/
abbrev BIIFToggleBitSig := T → Nat → T

/-- Signature for `bIIF_and`: pointwise AND. -/
abbrev BIIFAndSig := T → T → T

/-- Signature for `bIIF_or`: pointwise OR. -/
abbrev BIIFOrSig := T → T → T

/-- Signature for `bIIF_xor`: pointwise XOR. -/
abbrev BIIFXorSig := T → T → T

/-- Signature for `bIIF_not`: pointwise NOT. -/
abbrev BIIFNotSig := T → T

end VerifiedBitmasks

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ──────────────────────────────────────────

-- !benchmark @start code_aux def=bIIF_newZeros
-- !benchmark @end code_aux def=bIIF_newZeros

def bIIF_newZeros : VerifiedBitmasks.BIIFNewZerosSig :=
-- !benchmark @start code def=bIIF_newZeros
  fun M => bitmask_new_zeros M
-- !benchmark @end code def=bIIF_newZeros

-- !benchmark @start code_aux def=bIIF_newOnes
-- !benchmark @end code_aux def=bIIF_newOnes

def bIIF_newOnes : VerifiedBitmasks.BIIFNewOnesSig :=
-- !benchmark @start code def=bIIF_newOnes
  fun M => bitmask_new_ones M
-- !benchmark @end code def=bIIF_newOnes

-- !benchmark @start code_aux def=bIIF_nbits
-- !benchmark @end code_aux def=bIIF_nbits

def bIIF_nbits : VerifiedBitmasks.BIIFNbitsSig :=
-- !benchmark @start code def=bIIF_nbits
  fun A => bitmask_nbits A
-- !benchmark @end code def=bIIF_nbits

-- !benchmark @start code_aux def=bIIF_popcnt
-- !benchmark @end code_aux def=bIIF_popcnt

def bIIF_popcnt : VerifiedBitmasks.BIIFPopcntSig :=
-- !benchmark @start code def=bIIF_popcnt
  fun A => bitmask_popcnt A
-- !benchmark @end code def=bIIF_popcnt

-- !benchmark @start code_aux def=bIIF_getBit
-- !benchmark @end code_aux def=bIIF_getBit

def bIIF_getBit : VerifiedBitmasks.BIIFGetBitSig :=
-- !benchmark @start code def=bIIF_getBit
  fun A i => bitmask_get_bit A i
-- !benchmark @end code def=bIIF_getBit

-- !benchmark @start code_aux def=bIIF_setBit
-- !benchmark @end code_aux def=bIIF_setBit

def bIIF_setBit : VerifiedBitmasks.BIIFSetBitSig :=
-- !benchmark @start code def=bIIF_setBit
  fun A i => bitmask_set_bit A i
-- !benchmark @end code def=bIIF_setBit

-- !benchmark @start code_aux def=bIIF_clearBit
-- !benchmark @end code_aux def=bIIF_clearBit

def bIIF_clearBit : VerifiedBitmasks.BIIFClearBitSig :=
-- !benchmark @start code def=bIIF_clearBit
  fun A i => bitmask_clear_bit A i
-- !benchmark @end code def=bIIF_clearBit

-- !benchmark @start code_aux def=bIIF_toggleBit
-- !benchmark @end code_aux def=bIIF_toggleBit

def bIIF_toggleBit : VerifiedBitmasks.BIIFToggleBitSig :=
-- !benchmark @start code def=bIIF_toggleBit
  fun A i => bitmask_toggle_bit A i
-- !benchmark @end code def=bIIF_toggleBit

-- !benchmark @start code_aux def=bIIF_and
-- !benchmark @end code_aux def=bIIF_and

def bIIF_and : VerifiedBitmasks.BIIFAndSig :=
-- !benchmark @start code def=bIIF_and
  fun A B => bitmask_and A B
-- !benchmark @end code def=bIIF_and

-- !benchmark @start code_aux def=bIIF_or
-- !benchmark @end code_aux def=bIIF_or

def bIIF_or : VerifiedBitmasks.BIIFOrSig :=
-- !benchmark @start code def=bIIF_or
  fun A B => bitmask_or A B
-- !benchmark @end code def=bIIF_or

-- !benchmark @start code_aux def=bIIF_xor
-- !benchmark @end code_aux def=bIIF_xor

def bIIF_xor : VerifiedBitmasks.BIIFXorSig :=
-- !benchmark @start code def=bIIF_xor
  fun A B => bitmask_xor A B
-- !benchmark @end code def=bIIF_xor

-- !benchmark @start code_aux def=bIIF_not
-- !benchmark @end code_aux def=bIIF_not

def bIIF_not : VerifiedBitmasks.BIIFNotSig :=
-- !benchmark @start code def=bIIF_not
  fun A => bitmask_not A
-- !benchmark @end code def=bIIF_not
