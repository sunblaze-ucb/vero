-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Intervaltree.Impl.Merge

Interval-set algebra over half-open `[lo, hi)` intervals of `Int`: a
point `x` is contained iff `lo ≤ x ∧ x < hi`, and an interval is nonempty
iff `lo < hi`. A set of intervals is a `List Iv`; the point set it covers
is the union of the per-interval point sets (frozen `covered` predicate).

The API is `overlaps`, `mergeOverlaps`, and `chop`. `mergeOverlaps ivs`
returns the unique minimal set of disjoint intervals covering the same
point set as `ivs`, sorted by `lo` with strict gaps between consecutive
output intervals (touching intervals `[0,2),[2,4)` coalesce into `[0,4)`;
empty intervals are dropped).

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A half-open interval `[lo, hi)` over `Int`. Nonempty iff `lo < hi`. -/
structure Iv where
  lo : Int
  hi : Int
deriving DecidableEq, Repr, Inhabited

/-- Frozen membership: `covered x ivs` is `true` iff the point `x` lies in
    some interval of the set `ivs` (half-open semantics). This is the
    fixed anchor the specs are written against. -/
def covered (x : Int) (ivs : List Iv) : Bool :=
  ivs.any (fun iv => decide (iv.lo ≤ x ∧ x < iv.hi))

/-- Frozen total length (Lebesgue measure) of a set of intervals: the sum of
    the signed widths `hi - lo`. An anchor for the measure specs. -/
def totalLen (ivs : List Iv) : Int :=
  (ivs.map (fun iv => iv.hi - iv.lo)).sum

/-- Frozen clamped total length: the sum of the *nonnegative* widths
    `max(0, hi - lo)`, i.e. every empty interval contributes `0` rather than a
    negative width. An anchor for the measure specs. -/
def clampedTotalLen (ivs : List Iv) : Int :=
  (ivs.map (fun iv => if iv.lo < iv.hi then iv.hi - iv.lo else 0)).sum

/-- Frozen predicate: the list is a canonical disjoint set — every interval is
    nonempty (`lo < hi`) and there is a STRICT gap between each interval and the
    next (`l[i].hi < l[i+1].lo`). An anchor for the canonical-form specs. -/
def disjointSortedNonempty (ivs : List Iv) : Prop :=
  (∀ iv ∈ ivs, iv.lo < iv.hi) ∧
  (∀ (i : Nat) (h : i + 1 < ivs.length), (ivs[i]).hi < (ivs[i+1]).lo)

namespace Intervaltree

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `overlaps a b`: whether the two half-open intervals share a point. -/
abbrev OverlapsSig      := Iv → Iv → Bool

/-- `mergeOverlaps ivs`: the unique minimal set of disjoint intervals
    covering the same point set as `ivs`, sorted by `lo` with strict gaps
    between consecutive intervals (touching intervals are coalesced).
    Empty intervals are dropped. -/
abbrev MergeOverlapsSig := List Iv → List Iv

/-- `chop b e ivs`: remove the half-open range `[b, e)` from every interval
    in the set, splitting intervals that straddle the cut. -/
abbrev ChopSig          := Int → Int → List Iv → List Iv

end Intervaltree

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── overlaps ──────────────────────────────────────────────────

-- !benchmark @start code_aux def=overlaps
-- !benchmark @end code_aux def=overlaps

def Intervaltree.overlaps : Intervaltree.OverlapsSig :=
-- !benchmark @start code def=overlaps
  fun a b => decide (a.lo < b.hi ∧ b.lo < a.hi)
-- !benchmark @end code def=overlaps

-- ── mergeOverlaps ─────────────────────────────────────────────

-- !benchmark @start code_aux def=mergeOverlaps
/-- Reference-impl helper for `mergeOverlaps`. -/
def Intervaltree.insertByLo (iv : Iv) : List Iv → List Iv
  | [] => if iv.lo < iv.hi then [iv] else []
  | y :: ys =>
    if iv.lo < iv.hi then
      if iv.lo ≤ y.lo then iv :: y :: ys
      else y :: Intervaltree.insertByLo iv ys
    else y :: ys

/-- Reference-impl helper for `mergeOverlaps`. -/
def Intervaltree.sortByLo (ivs : List Iv) : List Iv :=
  ivs.foldr Intervaltree.insertByLo []

/-- Reference-impl helper for `mergeOverlaps`. -/
def Intervaltree.coalesce : List Iv → List Iv
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
    if y.lo ≤ x.hi then
      Intervaltree.coalesce ({ lo := x.lo, hi := if x.hi < y.hi then y.hi else x.hi } :: rest)
    else
      x :: Intervaltree.coalesce (y :: rest)
  termination_by l => l.length
-- !benchmark @end code_aux def=mergeOverlaps

def Intervaltree.mergeOverlaps : Intervaltree.MergeOverlapsSig :=
-- !benchmark @start code def=mergeOverlaps
  fun ivs => Intervaltree.coalesce (Intervaltree.sortByLo ivs)
-- !benchmark @end code def=mergeOverlaps

-- ── chop ──────────────────────────────────────────────────────

-- !benchmark @start code_aux def=chop
/-- Reference-impl helper for `chop`: remove the range `[b, e)` from a
    single interval. -/
def Intervaltree.chopOne (b e : Int) (iv : Iv) : List Iv :=
  let left  : List Iv := if iv.lo < b then [{ lo := iv.lo, hi := if iv.hi < b then iv.hi else b }] else []
  let right : List Iv := if e < iv.hi then [{ lo := if iv.lo < e then e else iv.lo, hi := iv.hi }] else []
  (left ++ right).filter (fun p => decide (p.lo < p.hi))
-- !benchmark @end code_aux def=chop

def Intervaltree.chop : Intervaltree.ChopSig :=
-- !benchmark @start code def=chop
  fun b e ivs => ivs.flatMap (Intervaltree.chopOne b e)
-- !benchmark @end code def=chop
