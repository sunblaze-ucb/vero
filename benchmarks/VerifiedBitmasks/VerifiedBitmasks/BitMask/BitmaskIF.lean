import VerifiedBitmasks.BitMask.BitmaskSpec

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.BitMask.BitmaskIF

Abstract bitmask interface (`BitmaskIF`), refined concretely by
`BitmaskSpec`.  The type `T` is aliased to `BitmaskSpec.T` (= `List Bool`),
and all spec helpers delegate to the canonical `BitmaskSpec` definitions.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies (inside the `!benchmark code` markers).
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types (no markers — fixed vocabulary) ──────────────────────────────────

namespace BitmaskIF

/-- The bitmask type: identical to the canonical `BitmaskSpec.T`. -/
abbrev T := BitmaskSpec.T

/-- Validity invariant — trivially true for the canonical model. -/
def Inv (A : T) : Prop := BitmaskSpec.Inv A

/-- All sizes are valid in the canonical model. -/
def ValidSize (n : Nat) : Prop := BitmaskSpec.ValidSize n

/-- Bit index `i` is valid if it is in bounds. -/
def ValidBit (A : T) (i : Nat) : Prop := BitmaskSpec.ValidBit A i

/-- Convert to the canonical bit sequence (identity). -/
def ToBitSeq (A : T) : List Bool := BitmaskSpec.ToBitSeq A

/-- Number of bits. -/
def bitmask_nbits (A : T) : Nat := BitmaskSpec.bitmask_nbits A

/-- Population count (number of set bits). -/
def bitmask_popcnt (A : T) : Nat := BitmaskSpec.bitmask_popcnt A

/-- Get the bit at position `i`. -/
def bitmask_get_bit (A : T) (i : Nat) : Bool := BitmaskSpec.bitmask_get_bit A i

/-- Set the bit at position `i`. -/
def bitmask_set_bit (A : T) (i : Nat) : T := BitmaskSpec.bitmask_set_bit A i

/-- Clear the bit at position `i`. -/
def bitmask_clear_bit (A : T) (i : Nat) : T := BitmaskSpec.bitmask_clear_bit A i

/-- Toggle the bit at position `i`. -/
def bitmask_toggle_bit (A : T) (i : Nat) : T := BitmaskSpec.bitmask_toggle_bit A i

/-- Extensional equality. -/
def bitmask_eq (A B : T) : Bool := BitmaskSpec.bitmask_eq A B

/-- Test whether all bits are zero. -/
def bitmask_is_zeros (A : T) : Bool := BitmaskSpec.bitmask_is_zeros A

/-- Test whether all bits are one. -/
def bitmask_is_ones (A : T) : Bool := BitmaskSpec.bitmask_is_ones A

/-- Bitwise AND. -/
def bitmask_and (A B : T) : T := BitmaskSpec.bitmask_and A B

/-- Bitwise OR. -/
def bitmask_or (A B : T) : T := BitmaskSpec.bitmask_or A B

/-- Bitwise XOR. -/
def bitmask_xor (A B : T) : T := BitmaskSpec.bitmask_xor A B

/-- Bitwise NOT. -/
def bitmask_not (A : T) : T := BitmaskSpec.bitmask_not A

end BitmaskIF

-- ── API signatures (no markers — fixed vocabulary) ─────────────────────────

namespace Bank

abbrev BitmaskIFNewZerosSig := Nat → BitmaskIF.T
abbrev BitmaskIFNewOnesSig  := Nat → BitmaskIF.T
abbrev BitmaskIFConcatSig   := BitmaskIF.T → BitmaskIF.T → BitmaskIF.T
abbrev BitmaskIFSplitSig    := BitmaskIF.T → Nat → BitmaskIF.T × BitmaskIF.T

end Bank

-- ── Implementation stubs (LLM task) ────────────────────────────────────────

-- !benchmark @start code_aux def=bIF_newZeros
-- !benchmark @end code_aux def=bIF_newZeros

def Bank.bIF_newZeros : Bank.BitmaskIFNewZerosSig :=
-- !benchmark @start code def=bIF_newZeros
  fun m => BitmaskSpec.bitmask_new_zeros m
-- !benchmark @end code def=bIF_newZeros

-- !benchmark @start code_aux def=bIF_newOnes
-- !benchmark @end code_aux def=bIF_newOnes

def Bank.bIF_newOnes : Bank.BitmaskIFNewOnesSig :=
-- !benchmark @start code def=bIF_newOnes
  fun m => BitmaskSpec.bitmask_new_ones m
-- !benchmark @end code def=bIF_newOnes

-- !benchmark @start code_aux def=bIF_concat
-- !benchmark @end code_aux def=bIF_concat

def Bank.bIF_concat : Bank.BitmaskIFConcatSig :=
-- !benchmark @start code def=bIF_concat
  fun a b => BitmaskSpec.bitmask_concat a b
-- !benchmark @end code def=bIF_concat

-- !benchmark @start code_aux def=bIF_split
-- !benchmark @end code_aux def=bIF_split

def Bank.bIF_split : Bank.BitmaskIFSplitSig :=
-- !benchmark @start code def=bIF_split
  fun a i => BitmaskSpec.bitmask_split a i
-- !benchmark @end code def=bIF_split
