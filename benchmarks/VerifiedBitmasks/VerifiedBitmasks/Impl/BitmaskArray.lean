import VerifiedBitmasks.Impl.BitmaskSpec

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.Impl.BitmaskArray

Array-based (`Array Bool`) implementation of the bitmask interface.
`BArr_T` is `Array Bool`; `BitmaskArray.I` interprets it as the canonical
`List Bool` representation used by the `BitmaskSpec` spec helpers.

Translated from `src/BitMask/BitmaskArray.i.dfy`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Type (no markers — fixed vocabulary) ──────────────────────────────────────

/-- Array-based bitmask type: an `Array Bool` where each element is one bit. -/
abbrev BArr_T := Array Bool

-- ── Spec helpers (frozen vocabulary, no markers) ──────────────────────────────

namespace BitmaskArray

/-- Invariant on the array bitmask (trivially True for Array Bool). -/
def Inv (_A : BArr_T) : Prop := True

/-- Interpretation function: convert Array Bool to List Bool. -/
def I (A : BArr_T) : List Bool := A.toList

end BitmaskArray

-- ── API signatures (no markers — fixed vocabulary) ────────────────────────────

namespace VerifiedBitmasks

/-- Signature for `bArr_cNewZeros`: create an all-zeros bitmask of n bits (array implementation). -/
abbrev BArrCNewZerosSig := UInt64 → BArr_T

/-- Signature for `bArr_cNewOnes`: create an all-ones bitmask of n bits (array implementation). -/
abbrev BArrCNewOnesSig := UInt64 → BArr_T

/-- Signature for `bArr_nbits`: return the number of bits as a UInt64. -/
abbrev BArrNbitsSig := BArr_T → UInt64

/-- Signature for `bArr_popcnt`: count set bits in the array bitmask. -/
abbrev BArrPopcntSig := BArr_T → UInt64

/-- Signature for `bArr_getBit`: get the value of bit i (array implementation). -/
abbrev BArrGetBitSig := BArr_T → UInt64 → Bool

/-- Signature for `bArr_setBit`: return a new array bitmask with bit i set to true. -/
abbrev BArrSetBitSig := BArr_T → UInt64 → BArr_T

/-- Signature for `bArr_clearBit`: return a new array bitmask with bit i set to false. -/
abbrev BArrClearBitSig := BArr_T → UInt64 → BArr_T

/-- Signature for `bArr_toggleBit`: return a new array bitmask with bit i toggled. -/
abbrev BArrToggleBitSig := BArr_T → UInt64 → BArr_T

/-- Signature for `bArr_eq`: boolean equality of two array bitmasks. -/
abbrev BArrEqSig := BArr_T → BArr_T → Bool

/-- Signature for `bArr_isZeros`: true iff all bits of the array bitmask are false. -/
abbrev BArrIsZerosSig := BArr_T → Bool

/-- Signature for `bArr_isOnes`: true iff all bits of the array bitmask are true. -/
abbrev BArrIsOnesSig := BArr_T → Bool

/-- Signature for `bArr_and`: pointwise AND of two array bitmasks. -/
abbrev BArrAndSig := BArr_T → BArr_T → BArr_T

/-- Signature for `bArr_or`: pointwise OR of two array bitmasks. -/
abbrev BArrOrSig := BArr_T → BArr_T → BArr_T

/-- Signature for `bArr_xor`: pointwise XOR of two array bitmasks. -/
abbrev BArrXorSig := BArr_T → BArr_T → BArr_T

/-- Signature for `bArr_not`: pointwise NOT of an array bitmask. -/
abbrev BArrNotSig := BArr_T → BArr_T

end VerifiedBitmasks

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ──────────────────────────────────────────

-- !benchmark @start code_aux def=bArr_cNewZeros
-- !benchmark @end code_aux def=bArr_cNewZeros

def bArr_cNewZeros : VerifiedBitmasks.BArrCNewZerosSig :=
-- !benchmark @start code def=bArr_cNewZeros
  fun n => (List.replicate n.toNat false).toArray
-- !benchmark @end code def=bArr_cNewZeros

-- !benchmark @start code_aux def=bArr_cNewOnes
-- !benchmark @end code_aux def=bArr_cNewOnes

def bArr_cNewOnes : VerifiedBitmasks.BArrCNewOnesSig :=
-- !benchmark @start code def=bArr_cNewOnes
  fun n => (List.replicate n.toNat true).toArray
-- !benchmark @end code def=bArr_cNewOnes

-- !benchmark @start code_aux def=bArr_nbits
-- !benchmark @end code_aux def=bArr_nbits

def bArr_nbits : VerifiedBitmasks.BArrNbitsSig :=
-- !benchmark @start code def=bArr_nbits
  fun A => A.size.toUInt64
-- !benchmark @end code def=bArr_nbits

-- !benchmark @start code_aux def=bArr_popcnt
-- !benchmark @end code_aux def=bArr_popcnt

def bArr_popcnt : VerifiedBitmasks.BArrPopcntSig :=
-- !benchmark @start code def=bArr_popcnt
  fun A => A.foldl (fun acc b => if b then acc + 1 else acc) 0
-- !benchmark @end code def=bArr_popcnt

-- !benchmark @start code_aux def=bArr_getBit
-- !benchmark @end code_aux def=bArr_getBit

def bArr_getBit : VerifiedBitmasks.BArrGetBitSig :=
-- !benchmark @start code def=bArr_getBit
  fun A i => A.getD i.toNat false
-- !benchmark @end code def=bArr_getBit

-- !benchmark @start code_aux def=bArr_setBit
-- !benchmark @end code_aux def=bArr_setBit

def bArr_setBit : VerifiedBitmasks.BArrSetBitSig :=
-- !benchmark @start code def=bArr_setBit
  fun A i =>
    if i.toNat < A.size then A.set! i.toNat true else A
-- !benchmark @end code def=bArr_setBit

-- !benchmark @start code_aux def=bArr_clearBit
-- !benchmark @end code_aux def=bArr_clearBit

def bArr_clearBit : VerifiedBitmasks.BArrClearBitSig :=
-- !benchmark @start code def=bArr_clearBit
  fun A i =>
    if i.toNat < A.size then A.set! i.toNat false else A
-- !benchmark @end code def=bArr_clearBit

-- !benchmark @start code_aux def=bArr_toggleBit
-- !benchmark @end code_aux def=bArr_toggleBit

def bArr_toggleBit : VerifiedBitmasks.BArrToggleBitSig :=
-- !benchmark @start code def=bArr_toggleBit
  fun A i =>
    if i.toNat < A.size then A.set! i.toNat (!(A.getD i.toNat false)) else A
-- !benchmark @end code def=bArr_toggleBit

-- !benchmark @start code_aux def=bArr_eq
-- !benchmark @end code_aux def=bArr_eq

def bArr_eq : VerifiedBitmasks.BArrEqSig :=
-- !benchmark @start code def=bArr_eq
  fun A B => A == B
-- !benchmark @end code def=bArr_eq

-- !benchmark @start code_aux def=bArr_isZeros
-- !benchmark @end code_aux def=bArr_isZeros

def bArr_isZeros : VerifiedBitmasks.BArrIsZerosSig :=
-- !benchmark @start code def=bArr_isZeros
  fun A => A.all (· == false)
-- !benchmark @end code def=bArr_isZeros

-- !benchmark @start code_aux def=bArr_isOnes
-- !benchmark @end code_aux def=bArr_isOnes

def bArr_isOnes : VerifiedBitmasks.BArrIsOnesSig :=
-- !benchmark @start code def=bArr_isOnes
  fun A => A.all (· == true)
-- !benchmark @end code def=bArr_isOnes

-- !benchmark @start code_aux def=bArr_and
-- !benchmark @end code_aux def=bArr_and

def bArr_and : VerifiedBitmasks.BArrAndSig :=
-- !benchmark @start code def=bArr_and
  fun A B => Array.zipWith (· && ·) A B
-- !benchmark @end code def=bArr_and

-- !benchmark @start code_aux def=bArr_or
-- !benchmark @end code_aux def=bArr_or

def bArr_or : VerifiedBitmasks.BArrOrSig :=
-- !benchmark @start code def=bArr_or
  fun A B => Array.zipWith (· || ·) A B
-- !benchmark @end code def=bArr_or

-- !benchmark @start code_aux def=bArr_xor
-- !benchmark @end code_aux def=bArr_xor

def bArr_xor : VerifiedBitmasks.BArrXorSig :=
-- !benchmark @start code def=bArr_xor
  fun A B => Array.zipWith (fun a b => a != b) A B
-- !benchmark @end code def=bArr_xor

-- !benchmark @start code_aux def=bArr_not
-- !benchmark @end code_aux def=bArr_not

def bArr_not : VerifiedBitmasks.BArrNotSig :=
-- !benchmark @start code def=bArr_not
  fun A => A.map (!·)
-- !benchmark @end code def=bArr_not
