-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Compression.Impl.CoordinateCompression

Coordinate compression maps a collection of values to consecutive
integers 0 .. n−1 based on their sort order, enabling index-based
algorithms on arbitrary ordered types.

A `CoordinateCompressor α` is internally a sorted list of distinct
values (the *sorted unique* view of the input corpus).
- `compress` maps an original value to its 0-based rank (index in the
  sorted list), returning `none` if the value was never registered.
- `decompress` maps a rank back to the original value, returning
  `none` for out-of-range indices.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data type (DO NOT MODIFY) ─────────────────────────────

/-- A coordinate compressor for values of type `α`.
    Internally the sorted list of distinct registered values;
    index `i` in the list corresponds to compressed rank `i`. -/
abbrev CoordinateCompressor (α : Type _) := List α

namespace Compression

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev CoordDecompressSig (α : Type _) [Ord α] [BEq α] :=
  CoordinateCompressor α → Nat → Option α
abbrev CoordCompressSig (α : Type _) [Ord α] [BEq α] :=
  CoordinateCompressor α → α → Option Nat

end Compression

-- !benchmark @start global_aux
/-- Safe index into a `List α`; returns `none` for out-of-bounds. -/
private def coordGetOpt {α : Type _} : List α → Nat → Option α
  | [],     _     => none
  | a :: _, 0     => some a
  | _ :: t, n + 1 => coordGetOpt t n

/-- Return the first 0-based index at which `val` appears, or `none`. -/
private def coordIndexOf {α : Type _} [BEq α] (val : α) : List α → Option Nat
  | []      => none
  | x :: xs =>
    if x == val then some 0
    else (coordIndexOf val xs).map (· + 1)
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ──────────────────────────

-- !benchmark @start code_aux def=CoordinateCompressor.decompress
-- !benchmark @end code_aux def=CoordinateCompressor.decompress

def Compression.CoordinateCompressor.decompress {α : Type _} [Ord α] [BEq α]
    : Compression.CoordDecompressSig α :=
-- !benchmark @start code def=CoordinateCompressor.decompress
  fun self num => coordGetOpt self num
-- !benchmark @end code def=CoordinateCompressor.decompress

-- !benchmark @start code_aux def=CoordinateCompressor.compress
-- !benchmark @end code_aux def=CoordinateCompressor.compress

def Compression.CoordinateCompressor.compress {α : Type _} [Ord α] [BEq α]
    : Compression.CoordCompressSig α :=
-- !benchmark @start code def=CoordinateCompressor.compress
  fun self original => coordIndexOf original self
-- !benchmark @end code def=CoordinateCompressor.compress
