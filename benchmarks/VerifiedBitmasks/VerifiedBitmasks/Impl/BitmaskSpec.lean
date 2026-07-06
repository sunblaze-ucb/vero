-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.Impl.BitmaskSpec

Canonical mathematical model for bitmasks. A bitmask is represented as
`List Bool` (bit sequence, index 0 is the first bit). All operations here
are curator-given spec helpers — frozen vocabulary used by higher-level spec
files. There are no API slots: this module is the specification foundation.

Translated from `src/BitMask/Spec/BitmaskSpec.s.dfy`.

DO NOT MODIFY types or definitions — these are the fixed vocabulary.
Implement only the function bodies (none in this module).
-/

-- ── Foundation type (DO NOT MODIFY) ──────────────────────────────────────────

/-- Canonical bitmask type: a list of booleans (index 0 = first bit). -/
abbrev T := List Bool

-- ── BitmaskSpec namespace helpers (frozen vocabulary) ────────────────────────

namespace BitmaskSpec

/-- Identity coercion from nat to nat (used in spec statements). -/
def ToNat (n : Nat) : Nat := n

/-- Invariant on bitmask (trivially True for the `List Bool` model). -/
def Inv (_A : T) : Prop := True

/-- Predicate that any size is valid (trivially True for the `List Bool` model). -/
def ValidSize (_n : Nat) : Prop := True

/-- Predicate that bit index `i` is valid for bitmask `A`. -/
def ValidBit (A : T) (i : Nat) : Prop := i < A.length

/-- Identity conversion: `T` is already `List Bool`. -/
def ToBitSeq (A : T) : List Bool := A

end BitmaskSpec

-- ── Standalone spec helpers (frozen vocabulary) ───────────────────────────────

/-- Create a bitmask of `M` bits all set to false (all-zeros). -/
def bitmask_new_zeros (M : Nat) : T := List.replicate M false

/-- Create a bitmask of `M` bits all set to true (all-ones). -/
def bitmask_new_ones (M : Nat) : T := List.replicate M true

/-- Concatenate two bitmasks. -/
def bitmask_concat (A B : T) : T := A ++ B

/-- Split a bitmask at index `i` into two sub-bitmasks: `(A.take i, A.drop i)`. -/
def bitmask_split (A : T) (i : Nat) : T × T := (A.take i, A.drop i)

/-- Number of bits in the bitmask. -/
def bitmask_nbits (A : T) : Nat := A.length

/-- Count of set (`true`) bits in the bitmask (population count). -/
def bitmask_popcnt (A : T) : Nat := A.countP id

/-- Get the value of bit `i` in the bitmask (`false` if out of bounds). -/
def bitmask_get_bit (A : T) (i : Nat) : Bool := A.getD i false

/-- Set bit `i` to `true` in the bitmask. -/
def bitmask_set_bit (A : T) (i : Nat) : T := A.set i true

/-- Set bit `i` to `false` in the bitmask. -/
def bitmask_clear_bit (A : T) (i : Nat) : T := A.set i false

/-- Toggle (flip) bit `i` in the bitmask. -/
def bitmask_toggle_bit (A : T) (i : Nat) : T := A.set i (!A.getD i false)

/-- Boolean equality of two bitmasks (`true` iff the lists are equal). -/
def bitmask_eq (A B : T) : Bool := A == B

/-- `True` iff all bits in the bitmask are `false` (all-zeros). -/
def bitmask_is_zeros (A : T) : Prop := ∀ i, i < A.length → A.getD i false = false

/-- `True` iff all bits in the bitmask are `true` (all-ones). -/
def bitmask_is_ones (A : T) : Prop := ∀ i, i < A.length → A.getD i false = true

/-- Pointwise bitwise AND of two bitmasks. -/
def bitmask_and (A B : T) : T := List.zipWith (· && ·) A B

/-- Pointwise bitwise OR of two bitmasks. -/
def bitmask_or (A B : T) : T := List.zipWith (· || ·) A B

/-- Pointwise bitwise XOR of two bitmasks. -/
def bitmask_xor (A B : T) : T := List.zipWith (fun a b => a != b) A B

/-- Pointwise bitwise NOT of a bitmask. -/
def bitmask_not (A : T) : T := A.map (!·)

-- ── No API slots (all definitions above are frozen spec helpers) ──────────────
