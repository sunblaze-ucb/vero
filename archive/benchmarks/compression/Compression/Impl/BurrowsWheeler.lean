-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Compression.Impl.BurrowsWheeler

Burrows–Wheeler Transform (BWT): a lossless string transformation that
groups similar characters together, improving downstream compression.
The transform is fully reversible given only the position of the original
string in the sorted-rotations table.

Error-guarding on empty strings is handled gracefully (returns a default
rather than raising, since Lean has no exceptions).
DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- Result of a BWT: the transformed string and the rank of the
    original string in the sorted-rotations table. -/
structure BWTTransformDict where
  bwt_string          : String
  idx_original_string : Int
  deriving Repr, BEq

namespace Compression

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev AllRotationsSig := String → List String
abbrev BwtTransformSig := String → BWTTransformDict
abbrev ReverseBwtSig   := String → Int → String

end Compression

-- ── Shared helpers (fixed vocabulary, no markers) ────────────

/-- Find the 0-based index of the first occurrence of `x` in `xs`. -/
private def listFindIdx (xs : List String) (x : String) : Option Nat :=
  go xs 0
where
  go : List String → Nat → Option Nat
    | [],     _ => none
    | h :: t, n => if h == x then some n else go t (n + 1)

/-- Insert `s` into a lexicographically sorted list, maintaining order. -/
private def strInsert (s : String) : List String → List String
  | []       => [s]
  | h :: rest => if s < h then s :: h :: rest else h :: strInsert s rest

/-- Sort a `List String` in ascending lexicographic order (insertion sort). -/
private def strSort (xs : List String) : List String :=
  xs.foldl (fun acc s => strInsert s acc) []

/-- Safe index into a `List α`; returns `none` for out-of-bounds `n`. -/
private def listGetOpt {α : Type} : List α → Nat → Option α
  | [],     _     => none
  | a :: _, 0     => some a
  | _ :: t, n + 1 => listGetOpt t n

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ──────────────────────────

-- !benchmark @start code_aux def=all_rotations
-- !benchmark @end code_aux def=all_rotations

def Compression.all_rotations : Compression.AllRotationsSig :=
-- !benchmark @start code def=all_rotations
  fun s =>
    let chars := s.toList
    let n     := chars.length
    (List.range n).map (fun i =>
      String.ofList (chars.drop i ++ chars.take i))
-- !benchmark @end code def=all_rotations

-- !benchmark @start code_aux def=bwt_transform
-- !benchmark @end code_aux def=bwt_transform

def Compression.bwt_transform : Compression.BwtTransformSig :=
-- !benchmark @start code def=bwt_transform
  fun s =>
    if s.isEmpty then { bwt_string := "", idx_original_string := 0 }
    else
      let rotations := Compression.all_rotations s
      let sorted    := strSort rotations
      let bwtStr    := String.ofList (sorted.map (fun r => r.back))
      let idx       := (listFindIdx sorted s).map Int.ofNat |>.getD 0
      { bwt_string := bwtStr, idx_original_string := idx }
-- !benchmark @end code def=bwt_transform

-- !benchmark @start code_aux def=reverse_bwt
-- One BWT table-reconstruction step: prepend each BWT character to the
-- corresponding row, then sort lexicographically.
private def bwtStep (chars : List Char) (rows : List String) : List String :=
  strSort ((chars.zip rows).map (fun (c, r) => String.ofList (c :: r.toList)))
-- !benchmark @end code_aux def=reverse_bwt

def Compression.reverse_bwt : Compression.ReverseBwtSig :=
-- !benchmark @start code def=reverse_bwt
  fun bwt_string idx_original_string =>
    let chars := bwt_string.toList
    let n     := chars.length
    if n == 0 then ""
    else
      let init : List String := List.replicate n ""
      let rows := (List.range n).foldl (fun rows _ => bwtStep chars rows) init
      if idx_original_string < 0 then ""
      else listGetOpt rows idx_original_string.toNat |>.getD ""
-- !benchmark @end code def=reverse_bwt
