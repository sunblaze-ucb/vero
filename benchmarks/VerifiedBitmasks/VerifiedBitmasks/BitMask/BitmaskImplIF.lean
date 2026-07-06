import VerifiedBitmasks.BitMask.BitmaskIF

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.BitMask.BitmaskImplIF

Abstract intermediate bitmask interface (`BitmaskImplIF`), which extends
`BitmaskIF` with an interpretation function `I` that maps implementation
types back to the canonical `BitmaskSpec.T`.

All concrete bitmask implementations (`BitmaskFixedChunks`, `BitmaskSeq`,
`BitmaskArray`) refine this module by instantiating type `T` and `I`.

DO NOT MODIFY — curator-given vocabulary.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types / spec helpers (no markers — fixed vocabulary) ───────────────────

namespace BitmaskImplIF

/-- The abstract implementation type (concretely instantiated per module). -/
abbrev T := BitmaskIF.T

/-- The abstract integer type used for sizes/indices (Nat). -/
abbrev I_Type := Nat

/-- Validity invariant (delegates to BitmaskIF). -/
def Inv (A : T) : Prop := BitmaskIF.Inv A

/-- All sizes are valid (delegates to BitmaskIF). -/
def ValidSize (n : Nat) : Prop := BitmaskIF.ValidSize n

/-- Extensional equality (delegates to BitmaskIF). -/
def bitmask_eq (A B : T) : Bool := BitmaskIF.bitmask_eq A B

/-- Test whether all bits are zero (delegates to BitmaskIF). -/
def bitmask_is_zeros (A : T) : Bool := BitmaskIF.bitmask_is_zeros A

/-- Test whether all bits are one (delegates to BitmaskIF). -/
def bitmask_is_ones (A : T) : Bool := BitmaskIF.bitmask_is_ones A

/-- Create bitmask of `M` zeros (delegates to BitmaskSpec). -/
def bitmask_new_zeros (M : Nat) : T := BitmaskSpec.bitmask_new_zeros M

/-- Create bitmask of `M` ones (delegates to BitmaskSpec). -/
def bitmask_new_ones (M : Nat) : T := BitmaskSpec.bitmask_new_ones M

/-- Number of bits (delegates to BitmaskIF). -/
def bitmask_nbits (A : T) : Nat := BitmaskIF.bitmask_nbits A

/-- Population count (delegates to BitmaskIF). -/
def bitmask_popcnt (A : T) : Nat := BitmaskIF.bitmask_popcnt A

/-- Get the bit at position `i` (delegates to BitmaskIF). -/
def bitmask_get_bit (A : T) (i : Nat) : Bool := BitmaskIF.bitmask_get_bit A i

/-- Set the bit at position `i` (delegates to BitmaskIF). -/
def bitmask_set_bit (A : T) (i : Nat) : T := BitmaskIF.bitmask_set_bit A i

/-- Clear the bit at position `i` (delegates to BitmaskIF). -/
def bitmask_clear_bit (A : T) (i : Nat) : T := BitmaskIF.bitmask_clear_bit A i

/-- Toggle the bit at position `i` (delegates to BitmaskIF). -/
def bitmask_toggle_bit (A : T) (i : Nat) : T := BitmaskIF.bitmask_toggle_bit A i

/-- Bitwise AND (delegates to BitmaskIF). -/
def bitmask_and (A B : T) : T := BitmaskIF.bitmask_and A B

/-- Bitwise OR (delegates to BitmaskIF). -/
def bitmask_or (A B : T) : T := BitmaskIF.bitmask_or A B

/-- Bitwise XOR (delegates to BitmaskIF). -/
def bitmask_xor (A B : T) : T := BitmaskIF.bitmask_xor A B

/-- Bitwise NOT (delegates to BitmaskIF). -/
def bitmask_not (A : T) : T := BitmaskIF.bitmask_not A

end BitmaskImplIF
