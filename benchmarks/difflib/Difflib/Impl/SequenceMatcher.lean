-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Difflib.Impl.SequenceMatcher

Core sequence-matching operations. A sequence is a `List Nat` whose
elements are compared for equality only. The API surface:

* `findLongestMatch a b` — the single longest contiguous block `(i, j, k)`
  with `a[i:i+k] = b[j:j+k]`, chosen canonically.
* `getMatchingBlocks a b` — a list of maximal matching blocks, ending in
  the sentinel `(|a|, |b|, 0)`.
* `matchSize a b` — the length of the longest matching block.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A sequence to be matched: a `List Nat`. Elements are compared for
    equality only. -/
abbrev Sequence := List Nat

/-- A matching block `(i, j, k)`: `a[i:i+k]` equals `b[j:j+k]`, a common
    contiguous run of length `k` starting at index `i` in the first
    sequence and `j` in the second. -/
abbrev Block := Nat × Nat × Nat

namespace Difflib

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `findLongestMatch a b`: the single longest matching block of `a` and
    `b`, returned as `(i, j, k)`, chosen canonically (longest `k`; then
    smallest `i`; then smallest `j`). `(0, 0, 0)` when there is no common
    element. -/
abbrev FindLongestMatchSig := Sequence → Sequence → Block

/-- `getMatchingBlocks a b`: the list of maximal matching blocks describing
    the matching subsequences, monotonically increasing in `i` and `j`,
    terminated by the sentinel `(a.length, b.length, 0)`. -/
abbrev GetMatchingBlocksSig := Sequence → Sequence → List Block

/-- `matchSize a b`: the length `k` of the longest matching block — the
    contiguous-match size returned by `findLongestMatch`. -/
abbrev MatchSizeSig := Sequence → Sequence → Nat

end Difflib

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=findLongestMatch
/-- The length of the common run starting at the heads of `as`/`bs`:
    the largest `k` with `as.take k = bs.take k`. -/
def runLenFrom : Sequence → Sequence → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => if x == y then runLenFrom xs ys + 1 else 0

/-- The common-run length starting at index `i` in `a` and `j` in `b`:
    the largest `k` with `a[i:i+k] = b[j:j+k]`. -/
def commonRun (a b : Sequence) (i j : Nat) : Nat :=
  runLenFrom (a.drop i) (b.drop j)

/-- Is the candidate block `cand = (i, j, k)` strictly better than `best`
    under the canonical order — larger `k`, then smaller `i`, then smaller
    `j`? -/
def better (cand best : Block) : Bool :=
  let (i, j, k) := cand
  let (bi, bj, bk) := best
  k > bk || (k == bk && i < bi) || (k == bk && i == bi && j < bj)

/-- The canonically-best block `(i, j, commonRun a b i j)` over all start
    indices `i < a.length`, `j < b.length`, defaulting to `(0, 0, 0)`. -/
def scanBest (a b : Sequence) : Block :=
  (List.range a.length).foldl
    (fun best i =>
      (List.range b.length).foldl
        (fun best j =>
          let cand : Block := (i, j, commonRun a b i j)
          if better cand best then cand else best)
        best)
    [(0, 0, 0)].head!
-- !benchmark @end code_aux def=findLongestMatch

def Difflib.findLongestMatch : Difflib.FindLongestMatchSig :=
-- !benchmark @start code def=findLongestMatch
  fun a b => scanBest a b
-- !benchmark @end code def=findLongestMatch

-- !benchmark @start code_aux def=getMatchingBlocks
/-- Helper producing the matching blocks over the window
    `a[alo:ahi] × b[blo:bhi]`. `fuel` bounds the recursion depth. -/
def gmbAux (a b : Sequence) : Nat → Nat → Nat → Nat → Nat → List Block
  | 0, _, _, _, _ => []
  | fuel + 1, alo, ahi, blo, bhi =>
    if alo < ahi && blo < bhi then
      let sub := scanBest ((a.drop alo).take (ahi - alo)) ((b.drop blo).take (bhi - blo))
      let i := sub.1 + alo
      let j := sub.2.1 + blo
      let k := sub.2.2
      if k == 0 then []
      else
        gmbAux a b fuel alo i blo j ++ [(i, j, k)] ++ gmbAux a b fuel (i + k) ahi (j + k) bhi
    else []

/-- Insert `x` into a list of blocks ordered by `(i, j)` lexicographically. -/
def insertBlock (x : Block) : List Block → List Block
  | [] => [x]
  | y :: ys =>
    if x.1 < y.1 || (x.1 == y.1 && x.2.1 ≤ y.2.1) then x :: y :: ys
    else y :: insertBlock x ys

def sortBlocks : List Block → List Block
  | [] => []
  | x :: xs => insertBlock x (sortBlocks xs)
-- !benchmark @end code_aux def=getMatchingBlocks

def Difflib.getMatchingBlocks : Difflib.GetMatchingBlocksSig :=
-- !benchmark @start code def=getMatchingBlocks
  fun a b =>
    let blocks := sortBlocks (gmbAux a b (a.length + b.length + 1) 0 a.length 0 b.length)
    blocks ++ [(a.length, b.length, 0)]
-- !benchmark @end code def=getMatchingBlocks

-- !benchmark @start code_aux def=matchSize
-- !benchmark @end code_aux def=matchSize

def Difflib.matchSize : Difflib.MatchSizeSig :=
-- !benchmark @start code def=matchSize
  fun a b => (Difflib.findLongestMatch a b).2.2
-- !benchmark @end code def=matchSize
