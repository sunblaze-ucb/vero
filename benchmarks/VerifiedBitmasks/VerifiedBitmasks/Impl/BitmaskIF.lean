import VerifiedBitmasks.Impl.BitmaskSpec

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.Impl.BitmaskIF

Abstract bitmask interface concretized over `List Bool`. Spec helpers
(`BitmaskIF.Inv`, `ValidSize`, `ValidBit`, `ToBitSeq`, `bIF_eq`,
`bIF_isZeros`, `bIF_isOnes`) are frozen vocabulary that delegates to
`BitmaskSpec`. The fourteen API functions are LLM benchmark tasks.

Translated from `src/BitMask/Spec/BitmaskIF.s.dfy`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies (inside the `!benchmark code` markers).
-/

-- ── Spec helpers (frozen vocabulary, no markers) ────────────────────────────

namespace BitmaskIF

/-- Validity invariant — delegates to `BitmaskSpec.Inv` (trivially True). -/
def Inv (A : T) : Prop := BitmaskSpec.Inv A

/-- All sizes are valid in the canonical `List Bool` model. -/
def ValidSize (n : Nat) : Prop := BitmaskSpec.ValidSize n

/-- Bit index `i` is valid iff `i < A.length`. -/
def ValidBit (A : T) (i : Nat) : Prop := BitmaskSpec.ValidBit A i

/-- Convert to the canonical bit sequence (identity for `List Bool`). -/
def ToBitSeq (A : T) : List Bool := BitmaskSpec.ToBitSeq A

end BitmaskIF

/-- Boolean equality of two bitmasks — delegates to `bitmask_eq`. -/
def bIF_eq (A B : T) : Bool := bitmask_eq A B

/-- `true` iff all bits are `false` (all-zeros). -/
def bIF_isZeros (A : T) : Bool := A.all (· == false)

/-- `true` iff all bits are `true` (all-ones). -/
def bIF_isOnes (A : T) : Bool := A.all (· == true)

-- ── API signatures (no markers — fixed vocabulary) ─────────────────────────

namespace VerifiedBitmasks

abbrev BIFNewZerosSig  := Nat → T
abbrev BIFNewOnesSig   := Nat → T
abbrev BIFConcatSig    := T → T → T
abbrev BIFSplitSig     := T → Nat → T × T
abbrev BIFNbitsSig     := T → Nat
abbrev BIFPopcntSig    := T → Nat
abbrev BIFGetBitSig    := T → Nat → Bool
abbrev BIFSetBitSig    := T → Nat → T
abbrev BIFClearBitSig  := T → Nat → T
abbrev BIFToggleBitSig := T → Nat → T
abbrev BIFAndSig       := T → T → T
abbrev BIFOrSig        := T → T → T
abbrev BIFXorSig       := T → T → T
abbrev BIFNotSig       := T → T

end VerifiedBitmasks

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ────────────────────────────────────────

-- !benchmark @start code_aux def=bIF_newZeros
-- !benchmark @end code_aux def=bIF_newZeros

def VerifiedBitmasks.bIF_newZeros : VerifiedBitmasks.BIFNewZerosSig :=
-- !benchmark @start code def=bIF_newZeros
  fun M => bitmask_new_zeros M
-- !benchmark @end code def=bIF_newZeros

-- !benchmark @start code_aux def=bIF_newOnes
-- !benchmark @end code_aux def=bIF_newOnes

def VerifiedBitmasks.bIF_newOnes : VerifiedBitmasks.BIFNewOnesSig :=
-- !benchmark @start code def=bIF_newOnes
  fun M => bitmask_new_ones M
-- !benchmark @end code def=bIF_newOnes

-- !benchmark @start code_aux def=bIF_concat
-- !benchmark @end code_aux def=bIF_concat

def VerifiedBitmasks.bIF_concat : VerifiedBitmasks.BIFConcatSig :=
-- !benchmark @start code def=bIF_concat
  fun A B => bitmask_concat A B
-- !benchmark @end code def=bIF_concat

-- !benchmark @start code_aux def=bIF_split
-- !benchmark @end code_aux def=bIF_split

def VerifiedBitmasks.bIF_split : VerifiedBitmasks.BIFSplitSig :=
-- !benchmark @start code def=bIF_split
  fun A i => bitmask_split A i
-- !benchmark @end code def=bIF_split

-- !benchmark @start code_aux def=bIF_nbits
-- !benchmark @end code_aux def=bIF_nbits

def VerifiedBitmasks.bIF_nbits : VerifiedBitmasks.BIFNbitsSig :=
-- !benchmark @start code def=bIF_nbits
  fun A => bitmask_nbits A
-- !benchmark @end code def=bIF_nbits

-- !benchmark @start code_aux def=bIF_popcnt
-- !benchmark @end code_aux def=bIF_popcnt

def VerifiedBitmasks.bIF_popcnt : VerifiedBitmasks.BIFPopcntSig :=
-- !benchmark @start code def=bIF_popcnt
  fun A => bitmask_popcnt A
-- !benchmark @end code def=bIF_popcnt

-- !benchmark @start code_aux def=bIF_getBit
-- !benchmark @end code_aux def=bIF_getBit

def VerifiedBitmasks.bIF_getBit : VerifiedBitmasks.BIFGetBitSig :=
-- !benchmark @start code def=bIF_getBit
  fun A i => bitmask_get_bit A i
-- !benchmark @end code def=bIF_getBit

-- !benchmark @start code_aux def=bIF_setBit
-- !benchmark @end code_aux def=bIF_setBit

def VerifiedBitmasks.bIF_setBit : VerifiedBitmasks.BIFSetBitSig :=
-- !benchmark @start code def=bIF_setBit
  fun A i => bitmask_set_bit A i
-- !benchmark @end code def=bIF_setBit

-- !benchmark @start code_aux def=bIF_clearBit
-- !benchmark @end code_aux def=bIF_clearBit

def VerifiedBitmasks.bIF_clearBit : VerifiedBitmasks.BIFClearBitSig :=
-- !benchmark @start code def=bIF_clearBit
  fun A i => bitmask_clear_bit A i
-- !benchmark @end code def=bIF_clearBit

-- !benchmark @start code_aux def=bIF_toggleBit
-- !benchmark @end code_aux def=bIF_toggleBit

def VerifiedBitmasks.bIF_toggleBit : VerifiedBitmasks.BIFToggleBitSig :=
-- !benchmark @start code def=bIF_toggleBit
  fun A i => bitmask_toggle_bit A i
-- !benchmark @end code def=bIF_toggleBit

-- !benchmark @start code_aux def=bIF_and
-- !benchmark @end code_aux def=bIF_and

def VerifiedBitmasks.bIF_and : VerifiedBitmasks.BIFAndSig :=
-- !benchmark @start code def=bIF_and
  fun A B => bitmask_and A B
-- !benchmark @end code def=bIF_and

-- !benchmark @start code_aux def=bIF_or
-- !benchmark @end code_aux def=bIF_or

def VerifiedBitmasks.bIF_or : VerifiedBitmasks.BIFOrSig :=
-- !benchmark @start code def=bIF_or
  fun A B => bitmask_or A B
-- !benchmark @end code def=bIF_or

-- !benchmark @start code_aux def=bIF_xor
-- !benchmark @end code_aux def=bIF_xor

def VerifiedBitmasks.bIF_xor : VerifiedBitmasks.BIFXorSig :=
-- !benchmark @start code def=bIF_xor
  fun A B => bitmask_xor A B
-- !benchmark @end code def=bIF_xor

-- !benchmark @start code_aux def=bIF_not
-- !benchmark @end code_aux def=bIF_not

def VerifiedBitmasks.bIF_not : VerifiedBitmasks.BIFNotSig :=
-- !benchmark @start code def=bIF_not
  fun A => bitmask_not A
-- !benchmark @end code def=bIF_not
