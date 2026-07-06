-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Textdistance.Impl.Edit

Edit-distance operations over sequences of symbol codes.
`levenshtein a b` is the minimum number of single-symbol insertions,
deletions, and substitutions transforming `a` into `b`; `lcs a b` is the
length of the longest common subsequence. Sequences are `List Nat`;
distances and lengths are `Nat`.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A sequence is a list of symbol codes. -/
abbrev Symbols := List Nat

namespace Textdistance

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `levenshtein a b`: the minimum number of single-symbol insertions,
    deletions, and substitutions needed to transform `a` into `b`. -/
abbrev LevenshteinSig := Symbols → Symbols → Nat

/-- `lcs a b`: the length of the longest common subsequence of `a` and
    `b`. -/
abbrev LcsSig := Symbols → Symbols → Nat

end Textdistance

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=levenshtein
/-- Helper for `levenshtein`. -/
def Textdistance.levenshteinGo : Symbols → Symbols → Nat
  | [], b => b.length
  | a, [] => a.length
  | x :: xs, y :: ys =>
    if x == y then Textdistance.levenshteinGo xs ys
    else 1 + min (Textdistance.levenshteinGo xs (y :: ys))
                 (min (Textdistance.levenshteinGo (x :: xs) ys)
                      (Textdistance.levenshteinGo xs ys))
  termination_by a b => a.length + b.length
-- !benchmark @end code_aux def=levenshtein

def Textdistance.levenshtein : Textdistance.LevenshteinSig :=
-- !benchmark @start code def=levenshtein
  Textdistance.levenshteinGo
-- !benchmark @end code def=levenshtein

-- !benchmark @start code_aux def=lcs
/-- Helper for `lcs`. -/
def Textdistance.lcsGo : Symbols → Symbols → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
    if x == y then 1 + Textdistance.lcsGo xs ys
    else max (Textdistance.lcsGo xs (y :: ys)) (Textdistance.lcsGo (x :: xs) ys)
  termination_by a b => a.length + b.length
-- !benchmark @end code_aux def=lcs

def Textdistance.lcs : Textdistance.LcsSig :=
-- !benchmark @start code def=lcs
  Textdistance.lcsGo
-- !benchmark @end code def=lcs
