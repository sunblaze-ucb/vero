-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.BitMask.BitmaskSpec

Canonical mathematical model for bitmasks: a bitmask is a `List Bool`
(boolean sequence, LSB at index 0).  All operations here are curator-given
reference definitions used by higher-level spec files.

DO NOT MODIFY — curator-given vocabulary.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace BitmaskSpec

/-- Canonical bitmask type: a list of booleans (LSB at index 0). -/
abbrev T := List Bool

/-- Interpret a boolean list as an unsigned integer (LSB at index 0). -/
def ToNat (a : T) : Nat :=
  a.foldl (fun (acc, pow) b => (acc + if b then pow else 0, pow * 2)) (0, 1) |>.1

/-- Identity: the canonical representation is itself the bit sequence. -/
def ToBitSeq (a : T) : T := a

/-- Create a bitmask of `m` zero bits. -/
def bitmask_new_zeros (m : Nat) : T := List.replicate m false

/-- Create a bitmask of `m` one bits. -/
def bitmask_new_ones (m : Nat) : T := List.replicate m true

/-- Concatenate two bitmasks. -/
def bitmask_concat (a b : T) : T := a ++ b

/-- Split a bitmask at position `i`: returns `(a.take i, a.drop i)`. -/
def bitmask_split (a : T) (i : Nat) : T × T := (a.take i, a.drop i)

/-- Number of bits in the bitmask. -/
def bitmask_nbits (a : T) : Nat := a.length

/-- Count of set bits (population count). -/
def bitmask_popcnt (a : T) : Nat := a.countP id

/-- Get the bit at position `i` (false if out of range). -/
def bitmask_get_bit (a : T) (i : Nat) : Bool := a.getD i false

/-- Set the bit at position `i` to `true`. -/
def bitmask_set_bit (a : T) (i : Nat) : T :=
  a.mapIdx (fun j b => if j == i then true else b)

/-- Clear the bit at position `i` (set to `false`). -/
def bitmask_clear_bit (a : T) (i : Nat) : T :=
  a.mapIdx (fun j b => if j == i then false else b)

/-- Toggle the bit at position `i`. -/
def bitmask_toggle_bit (a : T) (i : Nat) : T :=
  a.mapIdx (fun j b => if j == i then !b else b)

/-- Bitwise AND: pointwise conjunction. -/
def bitmask_and (a b : T) : T := List.zipWith (· && ·) a b

/-- Bitwise OR: pointwise disjunction. -/
def bitmask_or (a b : T) : T := List.zipWith (· || ·) a b

/-- Bitwise XOR: pointwise exclusive-or. -/
def bitmask_xor (a b : T) : T := List.zipWith (· != ·) a b

/-- Bitwise NOT: pointwise negation. -/
def bitmask_not (a : T) : T := a.map (!·)

/-- Validity invariant: trivially true for the canonical model. -/
def Inv (_ : T) : Prop := True

/-- All sizes are valid in the canonical model. -/
def ValidSize (_ : Nat) : Prop := True

/-- Bit index `i` is valid if it is in bounds. -/
def ValidBit (a : T) (i : Nat) : Prop := i < a.length

/-- Extensional equality: two bitmasks are equal iff the lists are equal. -/
def bitmask_eq (a b : T) : Bool := a == b

/-- Test whether all bits are zero. -/
def bitmask_is_zeros (a : T) : Bool := a.all (!·)

/-- Test whether all bits are one. -/
def bitmask_is_ones (a : T) : Bool := a.all id

end BitmaskSpec
