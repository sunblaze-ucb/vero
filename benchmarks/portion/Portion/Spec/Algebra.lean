import Portion.Harness

/-!
# Portion.Spec.Algebra

Specifications for the interval-set Boolean algebra. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`; an API is always reached through
`impl.portion.<fn>`.

For every operation the obligation set pairs a **point-set semantics** half with
a **canonical-form** half:

* Semantics pins the operation's meaning against the frozen point-membership
  predicate `member` over all points `x : Int`, using frozen Boolean connectives
  (`union` on `∨`, `intersection` on `∧`, `complement` on `¬`, `difference` on
  `a ∧ ¬b`).
* Canonical-form pins the representation against the frozen `Canonical`
  predicate (the cut list is strictly increasing).

Both halves matter: membership alone admits non-canonical representations of the
right set; canonicality alone admits a canonical representation of the wrong
set. A uniqueness spec (`spec_canonical_unique`) pins each output to the one
canonical representative of its point set.

The frozen machinery below (`member`, `Canonical`) never refers to `impl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── Frozen ground-truth machinery (DO NOT MODIFY) ──────────────

/-- The frozen toggle-parity of the cuts that are `≤ x`: `true` iff an odd
    number of cut points lie at or below `x`. This is the specification's own
    ground truth, independent of any implementation. -/
def specCutParity (cuts : List Int) (x : Int) : Bool :=
  (cuts.filter (fun c => decide (c ≤ x))).length % 2 == 1

/-- Frozen point-membership: a point `x : Int` is in the set `s` iff the base
    parity `s.neg` (membership at `-∞`) is flipped an odd number of times by the
    cuts `≤ x`. This is THE point-set semantics the specs are written against. -/
def member (s : IntervalSet) (x : Int) : Bool :=
  s.neg != specCutParity s.cuts x

/-- Frozen canonical-form predicate: the cut list is strictly increasing. In
    this form the set is the unique sorted disjoint maximal atomic decomposition
    of its point set — there is no empty atom (a zero-width interval would need a
    repeated cut), no touching/overlapping pair, and the points are in order. The
    uniqueness half of the spec: two canonical sets with the same membership over
    *all* `x` are equal (`spec_canonical_unique`). -/
def Canonical (s : IntervalSet) : Prop :=
  List.Pairwise (· < ·) s.cuts

-- ════════════════════════════════════════════════════════════════
-- contains: the membership observer is pinned to the frozen semantics
-- ════════════════════════════════════════════════════════════════

/-- The public `contains` observer agrees with the frozen point-membership
    `member` on every set and point. This pins the observer the rest of the
    suite uses to read out an operation's point set: a wrong `contains` is
    rejected at some point, and a correct `contains` lets every membership `↔`
    spec below speak about the genuine point set. -/
def spec_contains_correct (impl : RepoImpl) : Prop :=
  ∀ (s : IntervalSet) (x : Int),
    impl.portion.contains s x = member s x

-- ════════════════════════════════════════════════════════════════
-- complement: ¬ semantics + canonical form + involution
-- ════════════════════════════════════════════════════════════════

/-- Complement semantics (frozen `¬`): a point is in `complement a` iff it is
    NOT in `a`, for every point. Anchored on Boolean negation over the unbounded
    `Int` universe — the defining property of set complement. -/
def spec_complement_member (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet) (x : Int),
    member (impl.portion.complement a) x = !(member a x)

/-- Complement preserves the canonical form: complementing a canonical set
    yields a canonical set. (The complement flips only the base parity at `-∞`;
    the cut list — hence its strict ordering — is untouched.) -/
def spec_complement_canonical (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet),
    Canonical a → Canonical (impl.portion.complement a)

/-- Complement is an involution on the point set: `complement (complement a)`
    has exactly the same members as `a`, for every point. The double-negation
    law of the Boolean algebra, stated against the frozen semantics. -/
def spec_complement_involutive (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet) (x : Int),
    member (impl.portion.complement (impl.portion.complement a)) x = member a x

-- ════════════════════════════════════════════════════════════════
-- union: ∨ semantics + canonical form
-- ════════════════════════════════════════════════════════════════

/-- Union semantics (frozen `∨`): a point is in `union a b` iff it is in `a` OR
    in `b`, for every point. The defining property of set union, anchored on
    Boolean disjunction over the unbounded `Int` universe. -/
def spec_union_member (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (x : Int),
    member (impl.portion.union a b) x = (member a x || member b x)

/-- Union output is canonical: the merged cut list is strictly increasing
    (sorted, disjoint, maximal). The uniqueness half — a representation covering
    the right point set but with a redundant/touching atom is rejected. -/
def spec_union_canonical (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    Canonical (impl.portion.union a b)

-- ════════════════════════════════════════════════════════════════
-- intersection: ∧ semantics + canonical form
-- ════════════════════════════════════════════════════════════════

/-- Intersection semantics (frozen `∧`): a point is in `intersection a b` iff it
    is in `a` AND in `b`, for every point. Anchored on Boolean conjunction over
    the unbounded `Int` universe. -/
def spec_intersection_member (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (x : Int),
    member (impl.portion.intersection a b) x = (member a x && member b x)

/-- Intersection output is canonical: the cut list is strictly increasing. -/
def spec_intersection_canonical (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    Canonical (impl.portion.intersection a b)

-- ════════════════════════════════════════════════════════════════
-- difference: a ∧ ¬b semantics + canonical form
-- ════════════════════════════════════════════════════════════════

/-- Difference semantics (frozen `a ∧ ¬b`): a point is in `difference a b` iff
    it is in `a` and NOT in `b`, for every point. The relative-complement
    property, anchored on `&&`/`!`. -/
def spec_difference_member (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (x : Int),
    member (impl.portion.difference a b) x = (member a x && !(member b x))

/-- Difference output is canonical: the cut list is strictly increasing. -/
def spec_difference_canonical (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    Canonical (impl.portion.difference a b)

-- ════════════════════════════════════════════════════════════════
-- Canonical-form UNIQUENESS
-- ════════════════════════════════════════════════════════════════

/-- **Uniqueness of the canonical representative.** Any `c` that is itself
    canonical (cuts strictly increasing) and covers exactly the same point set
    as `union a b` (membership equal at every point) IS the union's output:
    `union a b = c`. Once the canonical-form invariant is imposed there is no
    representational freedom for a given point set. -/
def spec_canonical_unique (impl : RepoImpl) : Prop :=
  ∀ (a b c : IntervalSet),
    Canonical c →
    (∀ x, member c x = member (impl.portion.union a b) x) →
      impl.portion.union a b = c

-- ════════════════════════════════════════════════════════════════
-- Algebra laws — EACH anchored to the point-set semantics
-- ════════════════════════════════════════════════════════════════

/-- Union is commutative on the point set (via `member`, not an abstract axiom):
    `union a b` and `union b a` have the same members everywhere. -/
def spec_union_comm (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (x : Int),
    member (impl.portion.union a b) x = member (impl.portion.union b a) x

/-- Intersection is commutative on the point set. -/
def spec_intersection_comm (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (x : Int),
    member (impl.portion.intersection a b) x = member (impl.portion.intersection b a) x

/-- Union is idempotent on the point set: `union a a` has the same members as
    `a` everywhere. -/
def spec_union_idem (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet) (x : Int),
    member (impl.portion.union a a) x = member a x

/-- Intersection is idempotent on the point set. -/
def spec_intersection_idem (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet) (x : Int),
    member (impl.portion.intersection a a) x = member a x

/-- Union is associative on the point set: nesting on the left and on the right
    cover the same points everywhere. -/
def spec_union_assoc (impl : RepoImpl) : Prop :=
  ∀ (a b c : IntervalSet) (x : Int),
    member (impl.portion.union (impl.portion.union a b) c) x
      = member (impl.portion.union a (impl.portion.union b c)) x

/-- Intersection is associative on the point set. -/
def spec_intersection_assoc (impl : RepoImpl) : Prop :=
  ∀ (a b c : IntervalSet) (x : Int),
    member (impl.portion.intersection (impl.portion.intersection a b) c) x
      = member (impl.portion.intersection a (impl.portion.intersection b c)) x

/-- Law of the excluded middle (complement is a complement, ⊤ side): the union
    of a set with its own complement covers *every* point — `member (union a
    (complement a)) x` is `true` for all `x`. Pins the universe `⊤`. -/
def spec_excluded_middle (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet) (x : Int),
    member (impl.portion.union a (impl.portion.complement a)) x = true

/-- Law of non-contradiction (complement is a complement, ∅ side): the
    intersection of a set with its own complement covers *no* point — `member
    (intersection a (complement a)) x` is `false` for all `x`. Pins the empty
    set `∅`. -/
def spec_non_contradiction (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet) (x : Int),
    member (impl.portion.intersection a (impl.portion.complement a)) x = false

/-- De Morgan (union side), via the point-set semantics: the complement of a
    union equals the intersection of the complements, member-for-member. -/
def spec_demorgan_union (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (x : Int),
    member (impl.portion.complement (impl.portion.union a b)) x
      = member (impl.portion.intersection (impl.portion.complement a) (impl.portion.complement b)) x

/-- De Morgan (intersection side): the complement of an intersection equals the
    union of the complements, member-for-member. -/
def spec_demorgan_intersection (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (x : Int),
    member (impl.portion.complement (impl.portion.intersection a b)) x
      = member (impl.portion.union (impl.portion.complement a) (impl.portion.complement b)) x

/-- Difference reduces to intersection-with-complement, on the point set:
    `difference a b` and `intersection a (complement b)` have the same members
    everywhere. Ties the relative complement to the primitive Boolean ops. -/
def spec_difference_as_inter_complement (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (x : Int),
    member (impl.portion.difference a b) x
      = member (impl.portion.intersection a (impl.portion.complement b)) x

/-- Distributivity of intersection over union, on the point set:
    `a & (b | c)` and `(a & b) | (a & c)` cover the same points everywhere. The
    lattice distributive law, anchored on the frozen semantics rather than an
    abstract axiom. -/
def spec_distrib_inter_over_union (impl : RepoImpl) : Prop :=
  ∀ (a b c : IntervalSet) (x : Int),
    member (impl.portion.intersection a (impl.portion.union b c)) x
      = member (impl.portion.union (impl.portion.intersection a b) (impl.portion.intersection a c)) x

-- ════════════════════════════════════════════════════════════════
-- isEmpty: structural emptiness ↔ no members
-- ════════════════════════════════════════════════════════════════

/-- `isEmpty` characterization, over **arbitrary** (not necessarily canonical)
    sets: `isEmpty s` reports `true` iff the set covers no point at all
    (`member s x = false` for every `x`). Ties the structural emptiness test to
    the frozen point-set semantics over the unbounded universe.

    There is deliberately **no** `Canonical s` precondition: `isEmpty` must give
    the right verdict even on a redundant representation (e.g. `⟨false, [3, 3]⟩`,
    which is empty as a point set but not strictly increasing). So the test
    cannot simply read off the raw `cuts` list being empty — it must decide
    emptiness of the underlying point set. -/
def spec_isEmpty_iff (impl : RepoImpl) : Prop :=
  ∀ (s : IntervalSet),
    impl.portion.isEmpty s = true ↔ ∀ x, member s x = false

-- ════════════════════════════════════════════════════════════════
-- LITERAL STRUCTURE EQUALITIES
--
-- The laws below state their end-facts as *literal equalities on the
-- `IntervalSet` structure* — the two `IntervalSet`s are equal as data (same
-- `neg`, same `cuts` list), not merely equal as point sets. Each is a clean
-- end-fact: a single `=` between two interval-set expressions. (Contrast the
-- `member … = member …` laws above, which only compare point-by-point
-- membership and say nothing about the representation.)
-- ════════════════════════════════════════════════════════════════

/-- `complement` is a structural involution on canonical sets: complementing
    twice returns the *literally equal* set (the base parity flips back and the
    cut list is untouched). Strictly stronger than the point-set involution
    `spec_complement_involutive`: it pins the representation, not just the
    membership. -/
def spec_complement_complement_eq (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet),
    impl.portion.complement (impl.portion.complement a) = a

/-- Union with self is the canonicalisation: for a *canonical* `a`, `union a a`
    returns `a` literally (same base parity, same cut list). Together with the
    semantics this says the operation, restricted to an already-canonical input,
    is the identity — its output is a stable canonical representative, not merely
    a coverage-equal one. -/
def spec_union_self_eq (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet),
    Canonical a → impl.portion.union a a = a

-- ════════════════════════════════════════════════════════════════
-- LITERAL STRUCTURE EQUALITIES — the full Boolean-algebra laws as data
--
-- Each law below is one literal `=` between two interval-set expressions, for
-- *arbitrary* inputs (no canonicality precondition). They restate the
-- point-set laws (excluded middle, non-contradiction, difference-as-relative-
-- complement, commutativity, De Morgan, associativity, distributivity, and a
-- normalisation fixpoint) one rung up: not "same members at every point" but
-- "the two operations return the literally-equal `IntervalSet`". A coverage-only
-- implementation that returns a differently-shaped (reordered, padded, or
-- duplicate-bearing) representation of the right point set satisfies the
-- `member … = member …` versions yet FAILS these.
-- ════════════════════════════════════════════════════════════════

/-- Excluded middle as a literal constant: the union of a set with its own
    complement is the *whole universe* `⟨true, []⟩` on the nose — same data, for
    every `a`. (`⟨true, []⟩` is the interval-set that is `true` at `-∞` with no
    toggle points, i.e. all of `Int`.) The literal counterpart of
    `spec_excluded_middle`. -/
def spec_excluded_middle_eq (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet),
    impl.portion.union a (impl.portion.complement a) = ⟨true, []⟩

/-- Non-contradiction as a literal constant: the intersection of a set with its
    own complement is the *empty set* `⟨false, []⟩` on the nose — same data, for
    every `a`. (`⟨false, []⟩` is `false` at `-∞` with no toggle points, i.e.
    nothing.) The literal counterpart of `spec_non_contradiction`. -/
def spec_non_contradiction_eq (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet),
    impl.portion.intersection a (impl.portion.complement a) = ⟨false, []⟩

/-- Difference is relative complement, literally: `difference a b` and
    `intersection a (complement b)` return the *literally-equal* interval-set for
    every `a`, `b`. The literal counterpart of
    `spec_difference_as_inter_complement`. -/
def spec_difference_as_inter_complement_eq (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    impl.portion.difference a b = impl.portion.intersection a (impl.portion.complement b)

/-- Union is commutative as data: `union a b` and `union b a` are the
    *literally-equal* interval-set, not merely point-equal. The literal
    counterpart of `spec_union_comm`. -/
def spec_union_comm_eq (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    impl.portion.union a b = impl.portion.union b a

/-- Intersection is commutative as data: `intersection a b` and `intersection b
    a` are the *literally-equal* interval-set. The literal counterpart of
    `spec_intersection_comm`. -/
def spec_intersection_comm_eq (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    impl.portion.intersection a b = impl.portion.intersection b a

/-- De Morgan (union side) as data: the complement of a union is the
    *literally-equal* interval-set to the intersection of the complements. The
    literal counterpart of `spec_demorgan_union`. -/
def spec_demorgan_union_eq (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    impl.portion.complement (impl.portion.union a b)
      = impl.portion.intersection (impl.portion.complement a) (impl.portion.complement b)

/-- Union is associative as data: nesting on the left and on the right return the
    *literally-equal* interval-set, for every `a`, `b`, `c`. The literal
    counterpart of `spec_union_assoc`. -/
def spec_union_assoc_eq (impl : RepoImpl) : Prop :=
  ∀ (a b c : IntervalSet),
    impl.portion.union (impl.portion.union a b) c
      = impl.portion.union a (impl.portion.union b c)

/-- Distributivity of intersection over union as data: `a & (b | c)` and `(a & b)
    | (a & c)` return the *literally-equal* interval-set, for every `a`, `b`,
    `c`. The literal counterpart of `spec_distrib_inter_over_union`. -/
def spec_distrib_inter_over_union_eq (impl : RepoImpl) : Prop :=
  ∀ (a b c : IntervalSet),
    impl.portion.intersection a (impl.portion.union b c)
      = impl.portion.union (impl.portion.intersection a b) (impl.portion.intersection a c)

/-- Normalisation fixpoint: a value produced by `union` is a stable canonical
    representative — re-unioning it with itself returns the *literally-equal*
    interval-set `union a b`, with no further reshaping (no reordering, padding,
    or duplicate cuts introduced or removed). Pins down "the output has no
    redundant cuts": there is nothing left to canonicalise. -/
def spec_union_canonical_fixpoint (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    impl.portion.union (impl.portion.union a b) (impl.portion.union a b)
      = impl.portion.union a b

-- ════════════════════════════════════════════════════════════════
-- LITERAL STRUCTURE EQUALITIES — intersection & difference side
--
-- The same literal-`=` end-facts for the `intersection` and `difference`
-- operations. A coverage-only implementation that returns a reordered, padded,
-- or duplicate-bearing representation of the right point set is rejected here
-- too, not just on the union side.
-- ════════════════════════════════════════════════════════════════

/-- Intersection with self is the canonicalisation: for a *canonical* `a`,
    `intersection a a` returns `a` literally (same base parity, same cut list).
    The literal counterpart of `spec_intersection_idem`: restricted to an
    already-canonical input the operation is the identity, returning the stable
    canonical representative rather than a merely coverage-equal one. -/
def spec_intersection_self_eq (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet),
    Canonical a → impl.portion.intersection a a = a

/-- Intersection is associative as data: nesting on the left and on the right
    return the *literally-equal* interval-set, for every `a`, `b`, `c`. The
    literal counterpart of `spec_intersection_assoc`. -/
def spec_intersection_assoc_eq (impl : RepoImpl) : Prop :=
  ∀ (a b c : IntervalSet),
    impl.portion.intersection (impl.portion.intersection a b) c
      = impl.portion.intersection a (impl.portion.intersection b c)

/-- De Morgan (intersection side) as data: the complement of an intersection is
    the *literally-equal* interval-set to the union of the complements, for
    every `a`, `b`. The literal counterpart of `spec_demorgan_intersection`
    (which only equated membership) — completing the literal-equality De Morgan
    pair alongside `spec_demorgan_union_eq`. -/
def spec_demorgan_intersection_eq (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    impl.portion.complement (impl.portion.intersection a b)
      = impl.portion.union (impl.portion.complement a) (impl.portion.complement b)

/-- Difference of a set with itself is the *empty set* `⟨false, []⟩` on the nose
    — same data, for every `a`. (`⟨false, []⟩` is `false` at `-∞` with no toggle
    points, i.e. nothing.) The literal self-annihilation law of relative
    complement: `a \ a = ∅`, pinned to the canonical empty representation. -/
def spec_difference_self_empty_eq (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet),
    impl.portion.difference a a = ⟨false, []⟩

/-- Difference with the empty set is the identity, literally: for a *canonical*
    `a`, `difference a ⟨false, []⟩` returns `a` itself (same base parity, same
    cut list). The literal right-identity law `a \ ∅ = a`, pinning the output to
    the stable canonical representative of `a` rather than a merely
    coverage-equal one. -/
def spec_difference_empty_id_eq (impl : RepoImpl) : Prop :=
  ∀ (a : IntervalSet),
    Canonical a → impl.portion.difference a ⟨false, []⟩ = a

-- ════════════════════════════════════════════════════════════════
-- WELL-DEFINEDNESS ON POINT SETS — the operation sees only the set,
-- not the representation
--
-- The clean end-fact below is a literal `=` on `IntervalSet`, but its hypotheses
-- talk only about point membership: if `a`/`a'` and `b`/`b'` are indistinguishable
-- through the frozen `member` predicate at every point, the two `union` outputs
-- are literally-equal data. No canonicality precondition on the inputs. This
-- pins union as a genuine function of the underlying point set.
-- ════════════════════════════════════════════════════════════════

/-- **Union is well-defined on point sets, up to literal representation.** If
    `a` and `a'` have the same members at every point, and `b` and `b'` likewise,
    then `union a b` and `union a' b'` are the *literally-equal* interval-set.
    Rejects any impl whose output representation depends on the input
    representation rather than only on the input point set. -/
def spec_union_wd_eq (impl : RepoImpl) : Prop :=
  ∀ (a a' b b' : IntervalSet),
    (∀ x, member a x = member a' x) → (∀ x, member b x = member b' x) →
      impl.portion.union a b = impl.portion.union a' b'

-- ════════════════════════════════════════════════════════════════
-- STRUCTURAL PROVENANCE — the output invents no cut points
--
-- Each law states, as a membership fact on the raw `cuts` list, that every
-- toggle point of the result is already a toggle point of one of the operands.
-- Together with the membership and canonical-form halves this closes the
-- "padding" escape: an impl cannot insert a cut point foreign to both inputs.
-- ════════════════════════════════════════════════════════════════

/-- Every cut of `union a b` is a cut of `a` or a cut of `b`: the union invents
    no toggle point. -/
def spec_union_cuts_from_inputs (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    ∀ c ∈ (impl.portion.union a b).cuts, c ∈ a.cuts ∨ c ∈ b.cuts

/-- Every cut of `intersection a b` is a cut of `a` or a cut of `b`. -/
def spec_intersection_cuts_from_inputs (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    ∀ c ∈ (impl.portion.intersection a b).cuts, c ∈ a.cuts ∨ c ∈ b.cuts

/-- Every cut of `difference a b` is a cut of `a` or a cut of `b`. -/
def spec_difference_cuts_from_inputs (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    ∀ c ∈ (impl.portion.difference a b).cuts, c ∈ a.cuts ∨ c ∈ b.cuts

-- ════════════════════════════════════════════════════════════════
-- MAXIMALITY — every cut is a genuine membership boundary
--
-- The `Canonical` predicate (cuts strictly increasing) forbids a repeated or
-- out-of-order cut, but a strictly-increasing list could still in principle
-- carry a cut across which membership does NOT change — a redundant toggle
-- point. The laws below rule that out at the point-set level: at every cut `c`
-- of the result, membership genuinely differs between `c` and `c - 1`
-- (`member r c = !(member r (c-1))`). This is the maximality half of the
-- canonical decomposition — no atom is empty, no two atoms touch.
-- ════════════════════════════════════════════════════════════════

/-- **Union maximality.** At every cut `c` of `union a b`, membership flips across
    `c`: `member (union a b) c = !(member (union a b) (c - 1))`. So no cut is
    redundant — the representation is the maximal atomic decomposition, with no
    empty or touching atom. -/
def spec_union_cut_boundary (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    ∀ c ∈ (impl.portion.union a b).cuts,
      member (impl.portion.union a b) c = !(member (impl.portion.union a b) (c - 1))

/-- **Intersection maximality.** At every cut `c` of `intersection a b`,
    membership flips across `c`. No cut is redundant. -/
def spec_intersection_cut_boundary (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    ∀ c ∈ (impl.portion.intersection a b).cuts,
      member (impl.portion.intersection a b) c
        = !(member (impl.portion.intersection a b) (c - 1))

/-- **Difference maximality.** At every cut `c` of `difference a b`, membership
    flips across `c`. No cut is redundant. -/
def spec_difference_cut_boundary (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    ∀ c ∈ (impl.portion.difference a b).cuts,
      member (impl.portion.difference a b) c
        = !(member (impl.portion.difference a b) (c - 1))

-- ════════════════════════════════════════════════════════════════
-- ADDITIONAL STRUCTURAL SIZE AND OBSERVATION LAWS
-- ════════════════════════════════════════════════════════════════

/-- Binary Boolean operations do not return more cuts than their two inputs
    contain in total. -/
def spec_binary_cut_length_le_inputs (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet),
    (impl.portion.union a b).cuts.length ≤ a.cuts.length + b.cuts.length ∧
    (impl.portion.intersection a b).cuts.length ≤ a.cuts.length + b.cuts.length ∧
    (impl.portion.difference a b).cuts.length ≤ a.cuts.length + b.cuts.length

/-- Binary Boolean operations do not return more occurrences of a cut value than
    their two inputs contain in total. -/
def spec_binary_cut_count_le_inputs (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (c : Int),
    List.count c ((impl.portion.union a b).cuts) ≤ List.count c a.cuts + List.count c b.cuts ∧
    List.count c ((impl.portion.intersection a b).cuts) ≤ List.count c a.cuts + List.count c b.cuts ∧
    List.count c ((impl.portion.difference a b).cuts) ≤ List.count c a.cuts + List.count c b.cuts

/-- The majority-of-three expression has no more cuts than the three inputs
    contain in total. -/
def spec_majority3_cut_length_le_inputs (impl : RepoImpl) : Prop :=
  ∀ (a b c : IntervalSet),
    let ab := impl.portion.intersection a b
    let ac := impl.portion.intersection a c
    let bc := impl.portion.intersection b c
    (impl.portion.union (impl.portion.union ab ac) bc).cuts.length
      ≤ a.cuts.length + b.cuts.length + c.cuts.length

/-- The exactly-one-of-three expression does not return more occurrences of a
    cut value than the three inputs contain in total. -/
def spec_exactly_one3_cut_count_le_inputs (impl : RepoImpl) : Prop :=
  ∀ (a b c : IntervalSet) (d : Int),
    let onlyA := impl.portion.difference a (impl.portion.union b c)
    let onlyB := impl.portion.difference b (impl.portion.union a c)
    let onlyC := impl.portion.difference c (impl.portion.union a b)
    List.count d ((impl.portion.union (impl.portion.union onlyA onlyB) onlyC).cuts)
      ≤ List.count d a.cuts + List.count d b.cuts + List.count d c.cuts

/-- Union membership agrees with a fold-based cut-count observer. -/
def spec_union_fold_member (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (x : Int),
    let foldMember := fun (s : IntervalSet) =>
      let n := s.cuts.foldl (fun k c => if c ≤ x then k + 1 else k) 0
      s.neg != (n % 2 == 1)
    foldMember (impl.portion.union a b) = (foldMember a || foldMember b)

/-- At the first cut of a union result, membership changes from the base value
    to its opposite. -/
def spec_union_head_boundary (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (h : Int),
    (impl.portion.union a b).cuts.head? = some h →
      member (impl.portion.union a b) (h - 1) = (impl.portion.union a b).neg ∧
      member (impl.portion.union a b) h = !((impl.portion.union a b).neg)

/-- Union with an empty left input does not add occurrences of cut values beyond
    the right input. -/
def spec_union_empty_left_cut_count (impl : RepoImpl) : Prop :=
  ∀ (z a : IntervalSet) (c : Int),
    impl.portion.isEmpty z = true →
      List.count c ((impl.portion.union z a).cuts) ≤ List.count c a.cuts

-- ════════════════════════════════════════════════════════════════
-- CANONICAL-FORM UNIQUENESS beyond union, and the pure bridge
--
-- The one canonical representative of a point set is fixed by its membership.
-- These pin that end-fact for the non-union APIs and, at the pure level, for
-- any two canonical sets.
-- ════════════════════════════════════════════════════════════════

/-- Canonical-representative uniqueness for the non-union APIs. Any canonical
    `c` that covers exactly the point set of `complement a` (for canonical `a`),
    of `intersection a b`, or of `difference a b` IS that output as literal
    data. The union-side counterpart is `spec_canonical_unique`. -/
def spec_nonunion_canonical_unique (impl : RepoImpl) : Prop :=
  (∀ (a c : IntervalSet),
    Canonical a → Canonical c →
    (∀ x, member c x = member (impl.portion.complement a) x) →
      impl.portion.complement a = c) ∧
  (∀ (a b c : IntervalSet),
    Canonical c →
    (∀ x, member c x = member (impl.portion.intersection a b) x) →
      impl.portion.intersection a b = c) ∧
  (∀ (a b c : IntervalSet),
    Canonical c →
    (∀ x, member c x = member (impl.portion.difference a b) x) →
      impl.portion.difference a b = c)

-- ════════════════════════════════════════════════════════════════
-- N-ARY LAWS over an arbitrary `List IntervalSet`
--
-- The binary operations lift to a fold over a list of any length; membership
-- of the fold is the n-ary Boolean combination, and De Morgan holds at the
-- n-ary level as literal data.
-- ════════════════════════════════════════════════════════════════

/-- A point is in the left-fold of `union` over any list of sets (from the empty
    set `⟨false, []⟩`) iff it is in at least one of them: n-ary disjunction of
    membership. -/
def spec_big_union_member (impl : RepoImpl) : Prop :=
  ∀ (sets : List IntervalSet) (x : Int),
    member (sets.foldl impl.portion.union ⟨false, []⟩) x =
      sets.any (fun s => member s x)

/-- N-ary De Morgan as data: the complement of the fold-`union` of any list of
    sets is the *literally-equal* interval-set to the fold-`intersection` (from
    the universe `⟨true, []⟩`) of their complements. -/
def spec_big_demorgan_union_eq (impl : RepoImpl) : Prop :=
  ∀ (sets : List IntervalSet),
    impl.portion.complement (sets.foldl impl.portion.union ⟨false, []⟩) =
      (sets.map impl.portion.complement).foldl impl.portion.intersection ⟨true, []⟩

/-- A point is in the left-fold of `intersection` over any list of sets (from the
    universe `⟨true, []⟩`) iff it is in all of them, and the fold output is
    canonical: n-ary conjunction of membership in strictly-increasing form. -/
def naryAllMember (ss : List IntervalSet) (x : Int) : Bool :=
  ss.foldl (fun acc s => acc && member s x) true

def spec_fold_intersection_member_and_canonical (impl : RepoImpl) : Prop :=
  ∀ (ss : List IntervalSet),
    let r := ss.foldl (fun acc s => impl.portion.intersection acc s)
      ({ neg := true, cuts := [] } : IntervalSet)
    Canonical r ∧ ∀ x, member r x = naryAllMember ss x

-- ════════════════════════════════════════════════════════════════
-- WELL-DEFINEDNESS ON POINT SETS — intersection & difference side
--
-- The union counterpart is `spec_union_wd_eq`; these carry the same end-fact to
-- the other two binary APIs.
-- ════════════════════════════════════════════════════════════════

/-- `intersection` and `difference` are well-defined on point sets, up to literal
    representation: if `a`/`a'` and `b`/`b'` have the same members at every point,
    then `intersection a b = intersection a' b'` and `difference a b =
    difference a' b'` as data. Rejects any impl whose output shape depends on the
    input representation rather than only on the input point set. -/
def spec_intersection_difference_wd_eq (impl : RepoImpl) : Prop :=
  ∀ (a a' b b' : IntervalSet),
    (∀ x, member a x = member a' x) →
    (∀ x, member b x = member b' x) →
      impl.portion.intersection a b = impl.portion.intersection a' b' ∧
      impl.portion.difference a b = impl.portion.difference a' b'

-- ════════════════════════════════════════════════════════════════
-- CUT LIST = the exact boundary set
--
-- The output cut list is characterised both ways: every cut is an input cut
-- value where the pointwise combiner flips, and — for a canonical result — the
-- cut list is exactly the set of membership-boundary points.
-- ════════════════════════════════════════════════════════════════

def cutFromEitherInput (a b : IntervalSet) (c : Int) : Prop :=
  c ∈ a.cuts ∨ c ∈ b.cuts

def unionFlipAt (a b : IntervalSet) (c : Int) : Prop :=
  (member a c || member b c) ≠ (member a (c - 1) || member b (c - 1))

def intersectionFlipAt (a b : IntervalSet) (c : Int) : Prop :=
  (member a c && member b c) ≠ (member a (c - 1) && member b (c - 1))

def differenceFlipAt (a b : IntervalSet) (c : Int) : Prop :=
  (member a c && !(member b c)) ≠ (member a (c - 1) && !(member b (c - 1)))

/-- The cut set of `union a b` is *exactly* the input cut values at which union
    membership flips across `c - 1 → c`: a value is a cut iff it is a cut of `a`
    or `b` and the combined membership differs at `c` and `c - 1`. Both
    directions are pinned — no invented cut, no missed boundary. -/
def spec_union_cuts_exact_flips (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (c : Int),
    c ∈ (impl.portion.union a b).cuts ↔
      cutFromEitherInput a b c ∧ unionFlipAt a b c

/-- The cut set of `intersection a b` is *exactly* the input cut values at which
    intersection membership flips across `c - 1 → c`. -/
def spec_intersection_cuts_exact_flips (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (c : Int),
    c ∈ (impl.portion.intersection a b).cuts ↔
      cutFromEitherInput a b c ∧ intersectionFlipAt a b c

/-- The cut set of `difference a b` is *exactly* the input cut values at which
    difference membership flips across `c - 1 → c`. -/
def spec_difference_cuts_exact_flips (impl : RepoImpl) : Prop :=
  ∀ (a b : IntervalSet) (c : Int),
    c ∈ (impl.portion.difference a b).cuts ↔
      cutFromEitherInput a b c ∧ differenceFlipAt a b c

def boundaryAt (s : IntervalSet) (c : Int) : Prop :=
  member s c ≠ member s (c - 1)

/-- Output cut lists are *exactly* their membership-boundary points: for the
    complement of a canonical set and for each binary result, a value is a cut
    iff membership differs at `c` and `c - 1`. Every boundary is a cut and every
    cut is a boundary. -/
def spec_operation_cuts_exact_boundaries (impl : RepoImpl) : Prop :=
  (∀ (a : IntervalSet) (c : Int),
    Canonical a →
      let r := impl.portion.complement a
      c ∈ r.cuts ↔ boundaryAt r c) ∧
  (∀ (a b : IntervalSet) (c : Int),
    let u := impl.portion.union a b
    c ∈ u.cuts ↔ boundaryAt u c) ∧
  (∀ (a b : IntervalSet) (c : Int),
    let i := impl.portion.intersection a b
    c ∈ i.cuts ↔ boundaryAt i c) ∧
  (∀ (a b : IntervalSet) (c : Int),
    let d := impl.portion.difference a b
    c ∈ d.cuts ↔ boundaryAt d c)

