-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Portion.Impl.Algebra

Interval-set Boolean algebra: `union` (`|`), `intersection` (`&`),
`complement` (`~`), `difference` (`-`), plus `contains` and `isEmpty`.

An `IntervalSet` is `{ neg : Bool, cuts : List Int }` for a subset of `Int`
that changes membership at finitely many points: `neg` is the membership at
`-∞`, and `cuts` are the points where membership toggles. The membership of a
point `x` is `neg` XOR-ed with the parity of the cuts that are `≤ x`. In
canonical form `cuts` is strictly increasing.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Behaviour is pinned
by Spec/Algebra.lean.
-/

-- ── Core data type (DO NOT MODIFY) ───────────────────────────

/-- An interval-set over `Int` in toggle/parity form.

    `neg` is the membership at `-∞` (the leftmost ray); `cuts` are the toggle
    points. The membership of a point `x` is `neg` XOR-ed with the parity of
    `{ c ∈ cuts | c ≤ x }`. In canonical form `cuts` is strictly increasing. -/
structure IntervalSet where
  neg  : Bool
  cuts : List Int
deriving DecidableEq, Repr, Inhabited

namespace Portion

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `contains s x`: whether the point `x : Int` is a member of the set `s`. -/
abbrev ContainsSig     := IntervalSet → Int → Bool

/-- `complement s`: the set-complement `~s` — every point not in `s`. -/
abbrev ComplementSig   := IntervalSet → IntervalSet

/-- `union a b`: the set-union `a | b` in canonical atomic form. -/
abbrev UnionSig        := IntervalSet → IntervalSet → IntervalSet

/-- `intersection a b`: the set-intersection `a & b` in canonical atomic form. -/
abbrev IntersectionSig := IntervalSet → IntervalSet → IntervalSet

/-- `difference a b`: the set-difference `a - b` in canonical atomic form. -/
abbrev DifferenceSig   := IntervalSet → IntervalSet → IntervalSet

/-- `isEmpty s`: whether the set is empty (covers no point). -/
abbrev IsEmptySig      := IntervalSet → Bool

end Portion

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── contains ──────────────────────────────────────────────────

-- !benchmark @start code_aux def=contains
/-- The parity (odd-count) of the cuts that are `≤ x`. -/
def cutParity (cuts : List Int) (x : Int) : Bool :=
  (cuts.filter (fun c => decide (c ≤ x))).length % 2 == 1
-- !benchmark @end code_aux def=contains

def Portion.contains : Portion.ContainsSig :=
-- !benchmark @start code def=contains
  fun s x => s.neg != cutParity s.cuts x
-- !benchmark @end code def=contains

-- ── complement ────────────────────────────────────────────────

-- !benchmark @start code_aux def=complement
-- !benchmark @end code_aux def=complement

def Portion.complement : Portion.ComplementSig :=
-- !benchmark @start code def=complement
  fun s => { neg := !s.neg, cuts := s.cuts }
-- !benchmark @end code def=complement

-- ── union / intersection / difference: shared merge fold ──────

-- !benchmark @start code_aux def=union
def toggleInsert (x : Int) : List Int → List Int
  | [] => [x]
  | c :: cs =>
    if x < c then x :: c :: cs
    else if x == c then cs
    else c :: toggleInsert x cs

/-- Canonicalise a raw toggle list to its strictly-increasing representative. -/
def normCuts (cuts : List Int) : List Int :=
  cuts.foldr toggleInsert []

/-- Membership of `x` in a raw `IntervalSet`. -/
def memberAt (s : IntervalSet) (x : Int) : Bool :=
  s.neg != cutParity s.cuts x

def insertSet (x : Int) : List Int → List Int
  | [] => [x]
  | c :: cs =>
    if x < c then x :: c :: cs
    else if x == c then c :: cs
    else c :: insertSet x cs

/-- The deduplicated sorted union of two cut lists. -/
def mergePoints (as bs : List Int) : List Int :=
  bs.foldr insertSet (as.foldr insertSet [])

/-- Keep the points of `pts` at which `g` differs from the running value `prev`. -/
def emitGo (g : Int → Bool) (prev : Bool) : List Int → List Int
  | [] => []
  | p :: ps =>
    let cur := g p
    if cur == prev then emitGo g prev ps
    else p :: emitGo g cur ps

/-- Combine two interval-sets under the Boolean combiner `f`, point by point. -/
def mergeWith (f : Bool → Bool → Bool) (a b : IntervalSet) : IntervalSet :=
  let pts := mergePoints a.cuts b.cuts
  let g := fun x => f (memberAt a x) (memberAt b x)
  { neg := f a.neg b.neg, cuts := emitGo g (f a.neg b.neg) pts }
-- !benchmark @end code_aux def=union

def Portion.union : Portion.UnionSig :=
-- !benchmark @start code def=union
  fun a b => mergeWith (fun p q => p || q) a b
-- !benchmark @end code def=union

-- ── intersection ──────────────────────────────────────────────

-- !benchmark @start code_aux def=intersection
-- !benchmark @end code_aux def=intersection

def Portion.intersection : Portion.IntersectionSig :=
-- !benchmark @start code def=intersection
  fun a b => mergeWith (fun p q => p && q) a b
-- !benchmark @end code def=intersection

-- ── difference ────────────────────────────────────────────────

-- !benchmark @start code_aux def=difference
-- !benchmark @end code_aux def=difference

def Portion.difference : Portion.DifferenceSig :=
-- !benchmark @start code def=difference
  fun a b => mergeWith (fun p q => p && !q) a b
-- !benchmark @end code def=difference

-- ── isEmpty ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=isEmpty
-- !benchmark @end code_aux def=isEmpty

def Portion.isEmpty : Portion.IsEmptySig :=
-- !benchmark @start code def=isEmpty
  fun s => !s.neg && (normCuts s.cuts).isEmpty
-- !benchmark @end code def=isEmpty
