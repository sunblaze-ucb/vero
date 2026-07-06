import Intervaltree.Harness

/-!
# Intervaltree.Spec.Merge

Specifications for the interval-set operations. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; the API is always reached
through `impl.intervaltree.<fn>`, never by calling the reference
`Intervaltree.<fn>` directly.

The `mergeOverlaps` obligation set is coverage ∧ canonicality:
`spec_merge_coverage` pins the *same point set* (the union is preserved),
and `spec_merge_disjoint_strict` pins the *canonical form* — sorted,
nonempty, with STRICT gaps between consecutive intervals. The `overlaps`
and `chop` specs are anchored on the frozen `covered` predicate, tying
each operation to the half-open point-set semantics.

DO NOT MODIFY — frozen benchmark content.
-/

-- ── overlaps: symmetry + point-set characterization ────────────

/-- `overlaps` is symmetric. -/
def spec_overlaps_symm (impl : RepoImpl) : Prop :=
  ∀ (a b : Iv),
    impl.intervaltree.overlaps a b = impl.intervaltree.overlaps b a

/-- `overlaps a a` is pinned to its EXACT truth value for EVERY interval (no
    nonemptiness precondition): a genuine interval (`lo < hi`) overlaps itself
    and an empty one does not, so `overlaps a a = decide (a.lo < a.hi)`. -/
def spec_overlaps_self_nonempty (impl : RepoImpl) : Prop :=
  ∀ (a : Iv),
    impl.intervaltree.overlaps a a = decide (a.lo < a.hi)

/-- `overlaps` is irreflexive on empty intervals: an empty interval `[lo, hi)`
    with `lo ≥ hi` covers no point, so it does not overlap itself. -/
def spec_overlaps_self_empty (impl : RepoImpl) : Prop :=
  ∀ (a : Iv),
    ¬ a.lo < a.hi → impl.intervaltree.overlaps a a = false

/-- EXACT characterization of non-overlap: `overlaps a b = false` iff one
    interval lies entirely at or below the other — `a.hi ≤ b.lo` (a is left of
    b) OR `b.hi ≤ a.lo` (b is left of a). -/
def spec_overlaps_disjoint_false (impl : RepoImpl) : Prop :=
  ∀ (a b : Iv),
    impl.intervaltree.overlaps a b = false ↔ (a.hi ≤ b.lo ∨ b.hi ≤ a.lo)

/-- `overlaps a b` is `true` iff the two nonempty intervals share a
    point — the anchor tying `overlaps` to half-open `covered` semantics.
    The nonemptiness hypotheses are required: the point-set characterization
    only holds for genuine (nonempty) intervals. -/
def spec_overlaps_iff_common_point (impl : RepoImpl) : Prop :=
  ∀ (a b : Iv),
    a.lo < a.hi → b.lo < b.hi →
      (impl.intervaltree.overlaps a b = true ↔
        ∃ (x : Int), covered x [a] = true ∧ covered x [b] = true)

-- ── mergeOverlaps: coverage (witness) ──────────────────────────

/-- Coverage: the merged set covers exactly the same point set as the input,
    for every point and every input. Quantifying over all `x` pins the union to
    be preserved. Stated on arbitrary inputs (no all-nonempty hypothesis). -/
def spec_merge_coverage (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv) (x : Int),
    covered x (impl.intervaltree.mergeOverlaps ivs) = covered x ivs

-- ── mergeOverlaps: canonicality (strict-gap, load-bearing) ─────

/-- Canonicality: the merged output is nonempty per interval (`lo < hi`) and
    sorted with STRICT gaps between consecutive intervals
    (`out[i].hi < out[i+1].lo`). The strict `<` (not `≤`) pins the unique
    canonical form: touching runs must be coalesced. -/
def spec_merge_disjoint_strict (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    let out := impl.intervaltree.mergeOverlaps ivs
    (∀ iv ∈ out, iv.lo < iv.hi) ∧
    (∀ (i : Nat) (h : i + 1 < out.length), (out[i]).hi < (out[i+1]).lo)

-- ── mergeOverlaps: defining equations / boundary cases ─────────

/-- Boundary: merging the empty set yields the empty set. -/
def spec_merge_nil (impl : RepoImpl) : Prop :=
  impl.intervaltree.mergeOverlaps [] = []

/-- Boundary (precondition-free): merging a singleton is pinned for EVERY `a` —
    a nonempty interval is returned unchanged, an empty one is dropped to `[]`. -/
def spec_merge_singleton (impl : RepoImpl) : Prop :=
  ∀ (a : Iv),
    impl.intervaltree.mergeOverlaps [a] = (if a.lo < a.hi then [a] else [])

/-- Edge (exact emptiness criterion): the merged set is empty IFF every input
    interval is empty (`lo ≥ hi`). So the output is `[]` for *exactly* the
    all-empty inputs and nothing else. -/
def spec_merge_all_empty_nil (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    impl.intervaltree.mergeOverlaps ivs = [] ↔ (∀ iv ∈ ivs, ¬ iv.lo < iv.hi)

-- ── mergeOverlaps: output invariants ───────────────────────────

/-- Invariant (standalone companion to `spec_merge_disjoint_strict`): every
    interval in the merged output is nonempty. -/
def spec_merge_output_nonempty (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    ∀ iv ∈ impl.intervaltree.mergeOverlaps ivs, iv.lo < iv.hi

/-- Invariant: the merged output is STRICTLY increasing by `lo` — consecutive
    output intervals satisfy `out[i].lo < out[i+1].lo`. No two output intervals
    may share a lower endpoint. -/
def spec_merge_sorted_lo (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    let out := impl.intervaltree.mergeOverlaps ivs
    ∀ (i : Nat) (h : i + 1 < out.length), (out[i]).lo < (out[i+1]).lo

/-- Invariant: the merged interval count never exceeds the number of NONEMPTY
    inputs — merging may combine or drop intervals but never creates more than
    it started with. -/
def spec_merge_length_le (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    (impl.intervaltree.mergeOverlaps ivs).length
      ≤ (ivs.filter (fun iv => decide (iv.lo < iv.hi))).length

/-- Canonical-form fixpoint (idempotence): re-merging an already-merged set
    leaves its point set unchanged. -/
def spec_merge_idempotent (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv) (x : Int),
    covered x (impl.intervaltree.mergeOverlaps (impl.intervaltree.mergeOverlaps ivs))
      = covered x (impl.intervaltree.mergeOverlaps ivs)

-- ── chop: point-set effect ─────────────────────────────────────

/-- Removal: no point inside the chopped range `[b, e)` survives. -/
def spec_chop_removes (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv) (x : Int),
    b ≤ x → x < e → covered x (impl.intervaltree.chop b e ivs) = false

/-- EXACT pointwise effect of `chop` for EVERY point (precondition-free): a
    point survives chopping iff it was covered AND it is not in the cut range
    `[b, e)`, i.e. `covered x (chop b e ivs) = covered x ivs && !decide(b≤x<e)`. -/
def spec_chop_pointwise (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv) (x : Int),
    covered x (impl.intervaltree.chop b e ivs)
      = (covered x ivs && !decide (b ≤ x ∧ x < e))

/-- Empty cut range is identity on coverage: when `e ≤ b` the range `[b, e)`
    contains no point, so chopping it out changes no membership. -/
def spec_chop_empty_range_id (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv) (x : Int),
    e ≤ b →
      covered x (impl.intervaltree.chop b e ivs) = covered x ivs

/-- Idempotence: chopping the same range twice has the same point-set effect
    as chopping it once. Removing a range is a stable operation — re-applying the
    identical cut must not perturb which points are covered. -/
def spec_chop_idempotent (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv) (x : Int),
    covered x (impl.intervaltree.chop b e (impl.intervaltree.chop b e ivs))
      = covered x (impl.intervaltree.chop b e ivs)

-- ── mergeOverlaps: deep canonical-form laws ────────────────────
--
-- The specs below pin `mergeOverlaps` as a true canonical-form (normalisation)
-- operator, not merely a coverage-preserving one. Each demands a property that
-- only the *exact* canonical output (sorted, nonempty, strict-gap, measure-
-- minimal) satisfies; a coverage-only impl is rejected.

/-- Canonical-form fixpoint as a LIST EQUALITY (not merely coverage): merging an
    already-merged set is the literal identity — every interval, in the same
    order. Pins the representation, not just the point set. -/
def spec_merge_exact_idempotent (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    impl.intervaltree.mergeOverlaps (impl.intervaltree.mergeOverlaps ivs)
      = impl.intervaltree.mergeOverlaps ivs

/-- Measure upper bound: the total length of the merged set never exceeds the
    clamped total length of the input (`Σ max(0, hi - lo)`). Pins `mergeOverlaps`
    as measure-non-increasing. -/
def spec_merge_totalLen_le (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    totalLen (impl.intervaltree.mergeOverlaps ivs) ≤ clampedTotalLen ivs

/-- Measure conservation (equality) on an already-canonical input: when the
    input is itself a disjoint sorted-nonempty set (`disjointSortedNonempty`),
    the merged total length equals the input total length exactly. -/
def spec_merge_totalLen_disjoint_eq (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    disjointSortedNonempty ivs →
      totalLen (impl.intervaltree.mergeOverlaps ivs) = totalLen ivs

/-- Convex-hull lower endpoint is preserved: when the merged output is
    nonempty, its head's `lo` is a lower bound on every nonempty input
    interval's `lo`, AND it is realised by some nonempty input interval (it is
    not invented). So the leftmost coordinate of the union is preserved exactly —
    rejects an impl that shifts or fabricates the smallest start point. -/
def spec_merge_hull_lo (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv) (o : Iv) (rest : List Iv),
    impl.intervaltree.mergeOverlaps ivs = o :: rest →
      (∀ iv ∈ ivs, iv.lo < iv.hi → o.lo ≤ iv.lo) ∧
      (∃ iv ∈ ivs, iv.lo < iv.hi ∧ o.lo = iv.lo)

/-- Convex-hull upper endpoint survives coalescing: when the merged output is
    nonempty, the `hi` of its last interval is an upper bound on every nonempty
    input interval's `hi`, AND it is realised by some nonempty input interval.
    So the rightmost coordinate of the union is preserved exactly. -/
def spec_merge_hull_hi (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv) (pre : List Iv) (last : Iv),
    impl.intervaltree.mergeOverlaps ivs = pre ++ [last] →
      (∀ iv ∈ ivs, iv.lo < iv.hi → iv.hi ≤ last.hi) ∧
      (∃ iv ∈ ivs, iv.lo < iv.hi ∧ iv.hi = last.hi)

-- ── mergeOverlaps × chop: cross-API composition ────────────────

/-- Chop/merge interaction: the coverage of the merge of the chopped set is
    exactly the merged coverage with the cut range `[b, e)` removed. Pins how the
    two operations interact for every point — running them in this order leaves
    exactly the points that were covered and not cut out, with no spurious
    interference between the canonicalisation and the removal. -/
def spec_merge_chop_coverage (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv) (x : Int),
    covered x (impl.intervaltree.mergeOverlaps (impl.intervaltree.chop b e ivs))
      = (covered x (impl.intervaltree.mergeOverlaps ivs) && !decide (b ≤ x ∧ x < e))

/-- Order independence of the canonical form, as a LITERAL LIST EQUALITY:
    reversing the input produces the *same* merged output list — same intervals,
    same order — not merely the same point set. -/
def spec_merge_reverse_eq (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    impl.intervaltree.mergeOverlaps ivs
      = impl.intervaltree.mergeOverlaps ivs.reverse

-- ── mergeOverlaps: canonical-form UNIQUENESS laws ──────────────
--
-- The four specs below pin `mergeOverlaps` as the UNIQUE canonical representative
-- of a point set. Each states only an END equality (or per-output existence)
-- relating the canonical form to another set or to a second input.

/-- **Uniqueness of the canonical disjoint cover.** Any list `c` that is *itself*
    a canonical disjoint set (`disjointSortedNonempty`: nonempty, sorted, strict
    gaps) and covers exactly the same point set as `ivs` IS the merged output:
    `mergeOverlaps ivs = c`. So the canonical form is the *one and only*
    minimal-disjoint cover of a given point set. -/
def spec_merge_canonical_unique (impl : RepoImpl) : Prop :=
  ∀ (ivs c : List Iv),
    disjointSortedNonempty c →
    (∀ x, covered x c = covered x ivs) →
      impl.intervaltree.mergeOverlaps ivs = c

/-- **The canonical form is a function of the point set alone.** Two inputs that
    cover the same point set (for every point) merge to the *literally equal*
    output list — the same intervals in the same order. So `mergeOverlaps`
    factors through the point set: it forgets every detail of its input except
    which points are covered. -/
def spec_merge_coverage_determines (impl : RepoImpl) : Prop :=
  ∀ (a b : List Iv),
    (∀ x, covered x a = covered x b) →
      impl.intervaltree.mergeOverlaps a = impl.intervaltree.mergeOverlaps b

/-- **Every output interval's lower endpoint is an input lower endpoint.** For
    *every* interval `o` in the merged output (not just the head), `o.lo` is
    realised exactly by some nonempty input interval's `lo`. So merging never
    invents a left endpoint anywhere in the output. -/
def spec_merge_saturated_lo (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    ∀ o ∈ impl.intervaltree.mergeOverlaps ivs,
      ∃ iv ∈ ivs, iv.lo < iv.hi ∧ o.lo = iv.lo

/-- **Closure under union of already-merged pieces.** Merging the concatenation
    of two separately-merged sets equals merging the concatenation of the raw
    sets: `merge (merge xs ++ merge ys) = merge (xs ++ ys)`, as a literal list
    equality. So pre-canonicalising the pieces before combining them changes
    nothing about the final canonical form. -/
def spec_merge_concat_closure (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Iv),
    impl.intervaltree.mergeOverlaps
        (impl.intervaltree.mergeOverlaps xs ++ impl.intervaltree.mergeOverlaps ys)
      = impl.intervaltree.mergeOverlaps (xs ++ ys)

-- ── mergeOverlaps: canonical-form shape, per-output endpoints, set-algebra ──
--
-- A further round of deep canonical-form laws. Each is a clean END statement
-- about the shape of the canonical output, its per-interval endpoints, or how
-- the canonical form behaves under set-algebraic combinations of inputs.

/-- **The merged output is canonical, stated in one frozen predicate.** The
    output is `disjointSortedNonempty` — every interval nonempty AND strict gaps
    between consecutive ones — pinning the whole canonical shape at once. -/
def spec_merge_is_canonical (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    disjointSortedNonempty (impl.intervaltree.mergeOverlaps ivs)

/-- **Every output interval's upper endpoint is an input upper endpoint.** For
    *every* interval `o` in the merged output, `o.hi` is realised exactly by some
    nonempty input interval's `hi`. So merging never invents a right endpoint
    anywhere in the output. -/
def spec_merge_saturated_hi (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    ∀ o ∈ impl.intervaltree.mergeOverlaps ivs,
      ∃ iv ∈ ivs, iv.lo < iv.hi ∧ o.hi = iv.hi

/-- **Each output run is solid.** Every integer point strictly inside an output
    interval `o` (`o.lo ≤ x < o.hi`) is actually covered by the *input*: the
    canonical output introduces no spurious coverage — its interiors are exactly
    the input's covered points. Combined with the strict gaps, this says the
    output runs are precisely the maximal solid blocks of the input's point set. -/
def spec_merge_run_solid (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv) (x : Int),
    ∀ o ∈ impl.intervaltree.mergeOverlaps ivs,
      o.lo ≤ x → x < o.hi → covered x ivs = true

/-- **Each output run is left-maximal.** For every output interval `o`, the cell
    just left of its start, `o.lo - 1`, is NOT covered by the input. So each run
    begins exactly where the input's point set begins — you cannot extend any run
    one step to the left and stay inside the covered set. The right-open companion
    is `spec_merge_hi_uncovered`. -/
def spec_merge_lo_pred_uncovered (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    ∀ o ∈ impl.intervaltree.mergeOverlaps ivs,
      covered (o.lo - 1) ivs = false

/-- **Each output run is right-maximal.** For every output interval `o`, its open
    right endpoint `o.hi` is NOT covered by the input. So each run ends exactly
    where the input's point set ends — the half-open boundary `o.hi` is the first
    uncovered point after the run. The left companion is
    `spec_merge_lo_pred_uncovered`. -/
def spec_merge_hi_uncovered (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    ∀ o ∈ impl.intervaltree.mergeOverlaps ivs,
      covered o.hi ivs = false

/-- **The merged point set distributes over concatenation (union).** A point is
    covered by the merge of `xs ++ ys` iff it is covered by the merge of `xs` or
    the merge of `ys`. So `mergeOverlaps` is a union homomorphism on point sets:
    canonicalising a union equals the union of the canonicalisations, pointwise.
    Rejects an impl whose canonical form does not respect union of point sets. -/
def spec_merge_append_coverage (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Iv) (x : Int),
    covered x (impl.intervaltree.mergeOverlaps (xs ++ ys))
      = (covered x (impl.intervaltree.mergeOverlaps xs)
          || covered x (impl.intervaltree.mergeOverlaps ys))

/-- **Pre-merging the right operand of a union is absorbed.** Merging `xs`
    concatenated with the *already-merged* `ys` equals merging `xs ++ ys`
    directly, as a literal list equality. The one-sided companion to
    `spec_merge_concat_closure`; canonicalising one side before the union changes
    nothing about the final canonical form. -/
def spec_merge_concat_closure_right (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Iv),
    impl.intervaltree.mergeOverlaps (xs ++ impl.intervaltree.mergeOverlaps ys)
      = impl.intervaltree.mergeOverlaps (xs ++ ys)

/-- **Self-union is a fixpoint.** Merging the concatenation of the merged set with
    itself returns the merged set unchanged, as a literal list equality:
    `merge (merge ivs ++ merge ivs) = merge ivs`. The canonical form is idempotent
    under union with itself — duplicating every run and re-merging recovers the
    original representation exactly. -/
def spec_merge_self_union_idem (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    impl.intervaltree.mergeOverlaps
        (impl.intervaltree.mergeOverlaps ivs ++ impl.intervaltree.mergeOverlaps ivs)
      = impl.intervaltree.mergeOverlaps ivs

-- ── mergeOverlaps × chop: deeper cross-API list-equality laws ──

/-- **Pre-merging before chopping is absorbed.** Chopping the cut range `[b, e)`
    out of the *already-merged* set and re-merging equals chopping the raw set and
    merging, as a literal list equality:
    `merge (chop b e (merge ivs)) = merge (chop b e ivs)`. So canonicalising before
    a chop does not change the final canonical result. -/
def spec_merge_chop_merge (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv),
    impl.intervaltree.mergeOverlaps
        (impl.intervaltree.chop b e (impl.intervaltree.mergeOverlaps ivs))
      = impl.intervaltree.mergeOverlaps (impl.intervaltree.chop b e ivs)

/-- **Chop is idempotent up to the canonical form.** Chopping the same range
    twice and merging equals chopping once and merging, as a literal list
    equality: `merge (chop b e (chop b e ivs)) = merge (chop b e ivs)`. Removing
    the same range a second time leaves the canonical output unchanged. Stronger
    than the coverage-only `spec_chop_idempotent`: it pins the representation,
    not just the point set. -/
def spec_merge_chop_idempotent (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv),
    impl.intervaltree.mergeOverlaps
        (impl.intervaltree.chop b e (impl.intervaltree.chop b e ivs))
      = impl.intervaltree.mergeOverlaps (impl.intervaltree.chop b e ivs)

/-- **Chop-then-merge is a function of the point set alone.** Two inputs covering
    the same point set, after chopping the same range `[b, e)` and merging, yield
    the *literally equal* output list. So the chop-then-canonicalise pipeline
    depends only on which points its input covers, not on the input's
    representation. Rejects an impl whose chopped canonical form leaks
    representational detail of the input. -/
def spec_merge_chop_coverage_determines (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (a c : List Iv),
    (∀ x, covered x a = covered x c) →
      impl.intervaltree.mergeOverlaps (impl.intervaltree.chop b e a)
        = impl.intervaltree.mergeOverlaps (impl.intervaltree.chop b e c)

-- ── mergeOverlaps: per-point multiplicity, endpoint, positional laws ──
--
-- A final layer of canonical-form laws phrased over derived enumerations: the
-- per-point coverage MULTIPLICITY (a count, not the boolean `covered`), the
-- lower-endpoint list, and the positional prefix/suffix split at each output
-- start. Each is a clean END statement about the canonical output.

/-- Number of intervals in `ivs` that contain the point `x` (a count, the
    cardinality companion to the boolean `covered`). -/
def coveredCount (x : Int) (ivs : List Iv) : Nat :=
  (ivs.filter (fun iv => decide (iv.lo ≤ x ∧ x < iv.hi))).length

/-- The lower endpoints of a list of intervals, with multiplicity and order. -/
def loEndpoints (ivs : List Iv) : List Int :=
  ivs.map (fun iv => iv.lo)

/-- Every point lies in at most one merged interval. -/
def spec_merge_coveredCount_le_one (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv) (x : Int),
    coveredCount x (impl.intervaltree.mergeOverlaps ivs) ≤ 1

/-- The merged point count equals the input membership bit. -/
def spec_merge_coveredCount_exact (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv) (x : Int),
    coveredCount x (impl.intervaltree.mergeOverlaps ivs)
      = (if covered x ivs = true then 1 else 0)

/-- Merged lower endpoints have no duplicates. -/
def spec_merge_loEndpoints_nodup (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    List.Nodup (loEndpoints (impl.intervaltree.mergeOverlaps ivs))

/-- Each output start is covered by its suffix and not by its prefix. -/
def spec_merge_getElem?_lo_split (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv) (i : Nat) (o : Iv),
    let out := impl.intervaltree.mergeOverlaps ivs
    out[i]? = some o →
      covered o.lo (out.take i) = false ∧
      covered o.lo (out.drop i) = true

-- ── mergeOverlaps: permutation invariance + global gap structure ──
--
-- The canonical form depends only on the multiset of inputs, and its runs are
-- pairwise (not merely consecutively) separated with an explicit empty gap.

/-- **Permutation invariance.** Any two inputs that are permutations of one
    another merge to the *literally equal* output list. The canonical form is a
    function of the input multiset alone — every ordering detail is forgotten. -/
def spec_merge_perm_eq_any (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Iv),
    List.Perm xs ys →
      impl.intervaltree.mergeOverlaps xs = impl.intervaltree.mergeOverlaps ys

/-- **Global pairwise separation.** For *any* two output positions `i < j` (not
    just consecutive), the earlier run ends strictly before the later run begins:
    `out[i].hi < out[j].lo`. Every pair of distinct merged runs is strictly
    disjoint. -/
def spec_merge_pairwise_strict_gap_all (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    let out := impl.intervaltree.mergeOverlaps ivs
    ∀ (i j : Nat) (hi : i < out.length) (hj : j < out.length),
      i < j → (out[i]'hi).hi < (out[j]'hj).lo

/-- **Explicit gap between adjacent runs.** Between each pair of consecutive
    output intervals there is an integer point that lies at or after the earlier
    run's end, strictly before the next run's start, and is not covered by the
    output. The gap is genuinely empty, witnessed by a concrete point. -/
def spec_merge_consecutive_gap_witness (impl : RepoImpl) : Prop :=
  ∀ (ivs : List Iv),
    let out := impl.intervaltree.mergeOverlaps ivs
    ∀ (i : Nat) (h : i + 1 < out.length),
      ∃ (x : Int),
        (out[i]).hi ≤ x ∧ x < (out[i+1]).lo ∧ covered x out = false

-- ── mergeOverlaps × coverage: monotonicity + overlap coupling ──

/-- **Coverage monotonicity.** If every point covered by `xs` is covered by `ys`,
    then every point covered by the merge of `xs` is covered by the merge of
    `ys`. Canonicalisation is monotone under point-set inclusion. -/
def spec_merge_coverage_monotone (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Iv),
    (∀ x, covered x xs = true → covered x ys = true) →
      ∀ x,
        covered x (impl.intervaltree.mergeOverlaps xs) = true →
          covered x (impl.intervaltree.mergeOverlaps ys) = true

/-- **Overlapping inputs share one output run.** Two nonempty intervals that
    `overlaps` reports as intersecting are absorbed into a single interval of
    `mergeOverlaps [a, b]` that covers every point of both. -/
def spec_overlaps_merge_same_run (impl : RepoImpl) : Prop :=
  ∀ (a b : Iv),
    a.lo < a.hi → b.lo < b.hi →
      impl.intervaltree.overlaps a b = true →
        ∃ o, o ∈ impl.intervaltree.mergeOverlaps [a, b] ∧
          (∀ x, covered x [a] = true → covered x [o] = true) ∧
          (∀ x, covered x [b] = true → covered x [o] = true)

-- ── chop: whole-list frame (canonicality-preserving) ──────────
--
-- On a canonical input and a proper cut range, `chop` returns another canonical
-- set as a LIST — order, nonemptiness, and strict gaps are all preserved without
-- any re-merge.

/-- **Chop preserves canonicality.** Chopping a proper range `[b, e)` (`b < e`)
    out of a canonical set (`disjointSortedNonempty`) yields another canonical
    set. The whole-list disjoint-sorted-nonempty shape survives the cut. -/
def spec_chop_canonical_preserves_canonical (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv),
    b < e →
      disjointSortedNonempty ivs →
        disjointSortedNonempty (impl.intervaltree.chop b e ivs)

/-- **Chop preserves lo-order on a canonical set.** Chopping a proper range out
    of a canonical set leaves the output strictly increasing by `lo`. -/
def spec_chop_canonical_sorted_lo (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv),
    b < e →
      disjointSortedNonempty ivs →
        let out := impl.intervaltree.chop b e ivs
        ∀ (i : Nat) (h : i + 1 < out.length),
          (out[i]).lo < (out[i+1]).lo

/-- **Chop keeps a canonical set pairwise-separated.** After chopping a proper
    range out of a canonical set, any two output positions `i < j` satisfy
    `out[i].hi < out[j].lo` — global strict separation is preserved. -/
def spec_chop_canonical_pairwise_strict_gap (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv),
    b < e →
      disjointSortedNonempty ivs →
        let out := impl.intervaltree.chop b e ivs
        ∀ (i j : Nat) (hi : i < out.length) (hj : j < out.length),
          i < j → (out[i]'hi).hi < (out[j]'hj).lo

/-- **Chop of a canonical set is a merge fixpoint.** Chopping a proper range out
    of a canonical set produces a list that is already in canonical form:
    re-merging it is the literal identity. -/
def spec_chop_canonical_merge_fixpoint (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv),
    b < e →
      disjointSortedNonempty ivs →
        impl.intervaltree.mergeOverlaps (impl.intervaltree.chop b e ivs)
          = impl.intervaltree.chop b e ivs

-- ── chop: measure + multiplicity + union frame ────────────────

/-- **Chop is measure-non-increasing.** For a valid cut range (`b ≤ e`), the
    total length of the chopped set never exceeds the clamped total length of the
    input. Removing a range only shrinks measure. -/
def spec_chop_totalLen_le_clamped (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv),
    b ≤ e →
      totalLen (impl.intervaltree.chop b e ivs) ≤ clampedTotalLen ivs

/-- **Chop distributes over concatenation on point sets.** A point is covered by
    the chop of `xs ++ ys` iff it is covered by the chop of `xs` or of `ys`.
    Chop is a union homomorphism on coverage. -/
def spec_chop_append_coverage (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (xs ys : List Iv) (x : Int),
    covered x (impl.intervaltree.chop b e (xs ++ ys))
      = (covered x (impl.intervaltree.chop b e xs)
          || covered x (impl.intervaltree.chop b e ys))

/-- **Chop zeroes multiplicity inside the cut and preserves it outside.** For a
    valid cut range (`b ≤ e`), the covering multiplicity `coveredCount` of the
    chopped set is `0` at every point of `[b, e)` and equal to the input's
    multiplicity at every other point. -/
def spec_chop_coveredCount_cut_complement (impl : RepoImpl) : Prop :=
  ∀ (b e : Int) (ivs : List Iv) (x : Int),
    b ≤ e →
      coveredCount x (impl.intervaltree.chop b e ivs)
        = (if b ≤ x ∧ x < e then 0 else coveredCount x ivs)
