import PackagingVersion.Harness

/-!
# PackagingVersion.Spec.Version

Specifications for the version-ordering operations. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; the API is always reached
through `impl.packagingVersion.<fn>`, never by calling the reference
`PackagingVersion.<fn>` directly.

The specs pin the intended version order: the total-order axioms (totality,
reflexivity, antisymmetry, transitivity) force `verLe` to be a total preorder
whose induced equality is `verEq`; trailing-zero and tag-precedence anchors fix
the intended order among all compatible total orders; and `maxVer` / `minVer` /
`sortVers` are pinned by extremal, permutation, and sortedness obligations.
-/

namespace PackagingVersion.Spec

/-- Adjacent-sorted predicate (a core-only `List.Chain'` stand-in): every
    adjacent pair in the list is related by `R`. The empty and singleton
    lists are trivially sorted. -/
def Sorted (R : Ver → Ver → Prop) : List Ver → Prop
  | []            => True
  | [_]           => True
  | a :: b :: rest => R a b ∧ Sorted R (b :: rest)

-- ── total-order axioms ─────────────────────────────────────────

/-- Totality: any two versions are comparable. -/
def spec_le_total (impl : RepoImpl) : Prop :=
  ∀ (a b : Ver),
    impl.packagingVersion.verLe a b = true ∨
    impl.packagingVersion.verLe b a = true

/-- Reflexivity. -/
def spec_le_refl (impl : RepoImpl) : Prop :=
  ∀ (a : Ver), impl.packagingVersion.verLe a a = true

/-- Antisymmetry, relating `verLe` to `verEq`: mutual `≤` implies order-equal. -/
def spec_le_antisymm (impl : RepoImpl) : Prop :=
  ∀ (a b : Ver),
    impl.packagingVersion.verLe a b = true →
    impl.packagingVersion.verLe b a = true →
    impl.packagingVersion.verEq a b = true

/-- Transitivity. -/
def spec_le_trans (impl : RepoImpl) : Prop :=
  ∀ (a b c : Ver),
    impl.packagingVersion.verLe a b = true →
    impl.packagingVersion.verLe b c = true →
    impl.packagingVersion.verLe a c = true

-- ── canonicality anchor: trailing zeros ────────────────────────

/-- CANONICALITY anchor: trailing release zeros are invisible to the order. The
    first conjunct is the order-equality of a tuple with its zero-extension; the
    second is stronger — appending a run of zeros to the release leaves the
    comparison against an *arbitrary third version* `w` unchanged in **both**
    `verLe` directions. So trailing zeros are order-transparent everywhere, not
    merely self-equal. -/
def spec_release_trailing_zero (impl : RepoImpl) : Prop :=
  (∀ (e : Nat) (rel : List Nat) (zeros : List Nat) (p : PreTag),
      zeros.all (fun z => z == 0) = true →
      impl.packagingVersion.verEq ⟨e, rel, p⟩ ⟨e, rel ++ zeros, p⟩ = true)
  ∧ (∀ (e : Nat) (rel : List Nat) (zeros : List Nat) (p : PreTag) (w : Ver),
      zeros.all (fun z => z == 0) = true →
        impl.packagingVersion.verLe ⟨e, rel, p⟩ w
          = impl.packagingVersion.verLe ⟨e, rel ++ zeros, p⟩ w
        ∧ impl.packagingVersion.verLe w ⟨e, rel, p⟩
          = impl.packagingVersion.verLe w ⟨e, rel ++ zeros, p⟩)

-- ── tag-precedence anchor ──────────────────────────────────────

/-- Tag-precedence chain (strict). Within a fixed epoch and release the chain
    `dev < a < b < rc < final < post` holds strictly: each adjacent pair is `≤`
    AND not `verEq`. The strictness rules out a degenerate order that calls
    distinct tags mutually `≤`. -/
def spec_tag_precedence (impl : RepoImpl) : Prop :=
  ∀ (e : Nat) (rel : List Nat) (n : Nat),
    (impl.packagingVersion.verLe ⟨e, rel, .dev n⟩ ⟨e, rel, .a n⟩   = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .dev n⟩ ⟨e, rel, .a n⟩   = false) ∧
    (impl.packagingVersion.verLe ⟨e, rel, .a n⟩   ⟨e, rel, .b n⟩   = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .a n⟩   ⟨e, rel, .b n⟩   = false) ∧
    (impl.packagingVersion.verLe ⟨e, rel, .b n⟩   ⟨e, rel, .rc n⟩  = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .b n⟩   ⟨e, rel, .rc n⟩  = false) ∧
    (impl.packagingVersion.verLe ⟨e, rel, .rc n⟩  ⟨e, rel, .none'⟩ = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .rc n⟩  ⟨e, rel, .none'⟩ = false) ∧
    (impl.packagingVersion.verLe ⟨e, rel, .none'⟩ ⟨e, rel, .post n⟩ = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .none'⟩ ⟨e, rel, .post n⟩ = false)

-- ── cross-axis priority anchors ────────────────────────────────

/-- CROSS-AXIS priority (epoch > release/tag), strict. A strictly greater epoch
    strictly dominates the order regardless of the release tuple or tag: if
    `e1 < e2`, then `⟨e1, …⟩ ≤ ⟨e2, …⟩` AND the two are not `verEq`, for *any*
    releases and tags. So no release/tag difference can ever cancel an epoch gap
    — a higher epoch is always the newer version. -/
def spec_epoch_dominates (impl : RepoImpl) : Prop :=
  ∀ (e1 e2 : Nat) (r1 r2 : List Nat) (t1 t2 : PreTag),
    e1 < e2 →
      impl.packagingVersion.verLe ⟨e1, r1, t1⟩ ⟨e2, r2, t2⟩ = true ∧
      impl.packagingVersion.verEq ⟨e1, r1, t1⟩ ⟨e2, r2, t2⟩ = false

/-- CROSS-AXIS priority (release > tag), strict. Within a fixed epoch, a strictly
    smaller release tuple strictly dominates any tag difference: if the
    trailing-zero-trimmed release comparison `relCmp r1 r2` is `lt`, then
    `⟨e, r1, t1⟩ ≤ ⟨e, r2, t2⟩` AND the two are not `verEq`, for *any* tags. A tag
    difference can never cancel a release gap. Together with `spec_epoch_dominates`
    this fixes the lex priority epoch > release > tag. -/
def spec_release_dominates_tag (impl : RepoImpl) : Prop :=
  ∀ (e : Nat) (r1 r2 : List Nat) (t1 t2 : PreTag),
    relCmp r1 r2 = Ordering.lt →
      impl.packagingVersion.verLe ⟨e, r1, t1⟩ ⟨e, r2, t2⟩ = true ∧
      impl.packagingVersion.verEq ⟨e, r1, t1⟩ ⟨e, r2, t2⟩ = false

-- ── sortVers: permutation ∧ sorted ─────────────────────────────

/-- `sortVers xs` is a permutation of `xs` (nothing dropped/added/duplicated). -/
def spec_sort_perm (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver), (impl.packagingVersion.sortVers xs).Perm xs

/-- `sortVers xs` is sorted ascending under `verLe` (adjacent pairs ordered). -/
def spec_sort_sorted (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver),
    Sorted (fun a b => impl.packagingVersion.verLe a b = true)
      (impl.packagingVersion.sortVers xs)

-- ── maxVer: unique greatest ────────────────────────────────────

/-- `maxVer xs = some m` implies `m` is a member of `xs`, is `≥` every element
    of `xs` under `verLe`, AND is the UNIQUE greatest up to `verEq`: every other
    element `w ∈ xs` that also dominates all of `xs` is `verEq m`. The uniqueness
    clause turns "a greatest witness" into "the greatest element, unique up to
    order-equality" — so `maxVer` cannot return a non-tight dominator nor pick a
    member outside the tied-greatest class. This is exactly the guarantee a caller
    needs from a "newest version" query over a set of PEP 440 versions. -/
def spec_max_is_greatest (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (m : Ver),
    impl.packagingVersion.maxVer xs = some m →
      (m ∈ xs ∧ ∀ (v : Ver), v ∈ xs → impl.packagingVersion.verLe v m = true) ∧
      (∀ (w : Ver), w ∈ xs →
        (∀ (v : Ver), v ∈ xs → impl.packagingVersion.verLe v w = true) →
          impl.packagingVersion.verEq m w = true)

-- ── verEq is an equivalence ─────────────────────────────────────

/-- `verEq` is reflexive. -/
def spec_eq_refl (impl : RepoImpl) : Prop :=
  ∀ (a : Ver), impl.packagingVersion.verEq a a = true

/-- `verEq` is symmetric. -/
def spec_eq_symm (impl : RepoImpl) : Prop :=
  ∀ (a b : Ver),
    impl.packagingVersion.verEq a b = true →
    impl.packagingVersion.verEq b a = true

/-- `verEq` is transitive. -/
def spec_eq_trans (impl : RepoImpl) : Prop :=
  ∀ (a b c : Ver),
    impl.packagingVersion.verEq a b = true →
    impl.packagingVersion.verEq b c = true →
    impl.packagingVersion.verEq a c = true

/-- The induced equality is exactly mutual `≤`: `verEq a b` holds iff both
    `verLe a b` and `verLe b a`. Pins `verEq` as the order-equality of `verLe`
    (both directions), not an unrelated equality. -/
def spec_eq_iff_le_le (impl : RepoImpl) : Prop :=
  ∀ (a b : Ver),
    impl.packagingVersion.verEq a b = true ↔
      (impl.packagingVersion.verLe a b = true ∧
       impl.packagingVersion.verLe b a = true)

/-- Strict antisymmetry: if `a ≤ b` strictly (not order-equal), then `¬ b ≤ a`.
    Rules out an order that calls two distinct-as-versions but non-equal items
    mutually `≤`. -/
def spec_le_strict_antisymm (impl : RepoImpl) : Prop :=
  ∀ (a b : Ver),
    impl.packagingVersion.verLe a b = true →
    impl.packagingVersion.verEq a b = false →
    impl.packagingVersion.verLe b a = false

-- ── more cross-axis structure ───────────────────────────────────

/-- `verEq` pins all three comparison axes. Order-equal versions agree on the
    epoch, AND their releases compare `eq` under the trailing-zero-trimmed
    `relCmp`, AND their tags compare `eq` under `tagCmp`. So `verEq` cannot
    identify versions that differ on the release or tag axis by anything other
    than trailing release zeros. -/
def spec_eq_implies_epoch_eq (impl : RepoImpl) : Prop :=
  ∀ (a b : Ver),
    impl.packagingVersion.verEq a b = true →
      a.epoch = b.epoch ∧
      relCmp a.release b.release = Ordering.eq ∧
      tagCmp a.pre b.pre = Ordering.eq

/-- When epoch ties and the frozen trailing-zero-trimmed release comparison
    `relCmp r1 r2` is `eq`, the version order reduces to the tag comparison:
    `⟨e,r1,t1⟩ ≤ ⟨e,r2,t2⟩` iff `tagCmp t1 t2 ≠ .gt`. This pins the tag as the
    least-significant tie-break axis. -/
def spec_release_eq_reduces_to_tag (impl : RepoImpl) : Prop :=
  ∀ (e : Nat) (r1 r2 : List Nat) (t1 t2 : PreTag),
    relCmp r1 r2 = Ordering.eq →
      (impl.packagingVersion.verLe ⟨e, r1, t1⟩ ⟨e, r2, t2⟩ = true ↔
       tagCmp t1 t2 ≠ Ordering.gt)

-- ── trailing-zero canonicality: concrete `1 = 1.0.0` ────────────

/-- CANONICALITY (concrete). `1`, `1.0`, `1.0.0` are all order-equal: appending
    two trailing zeros to the release `[1]` yields an order-equal version, for
    any epoch and tag. A second concrete trailing-zero anchor distinct from the
    general law and the `[1] ~ [1,0]` anchor. -/
def spec_trailing_zero_concrete (impl : RepoImpl) : Prop :=
  ∀ (e : Nat) (t : PreTag),
    impl.packagingVersion.verEq ⟨e, [1], t⟩ ⟨e, [1, 0, 0], t⟩ = true

-- ── tag precedence: individual edges ───────────────────────────

/-- `dev` is the strictly LEAST tag. Within a fixed epoch and release a `dev`
    pre-release with *any* qualifier number is strictly below `a`, `b`, `rc`, the
    final release, and `post` — each with an *arbitrary independent* qualifier
    number (`≤` and not order-equal). Pins `dev` as the global tag minimum. -/
def spec_tag_dev_lt_final (impl : RepoImpl) : Prop :=
  ∀ (e : Nat) (rel : List Nat) (n m : Nat),
    (impl.packagingVersion.verLe ⟨e, rel, .dev n⟩ ⟨e, rel, .a m⟩   = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .dev n⟩ ⟨e, rel, .a m⟩   = false) ∧
    (impl.packagingVersion.verLe ⟨e, rel, .dev n⟩ ⟨e, rel, .b m⟩   = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .dev n⟩ ⟨e, rel, .b m⟩   = false) ∧
    (impl.packagingVersion.verLe ⟨e, rel, .dev n⟩ ⟨e, rel, .rc m⟩  = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .dev n⟩ ⟨e, rel, .rc m⟩  = false) ∧
    (impl.packagingVersion.verLe ⟨e, rel, .dev n⟩ ⟨e, rel, .none'⟩ = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .dev n⟩ ⟨e, rel, .none'⟩ = false) ∧
    (impl.packagingVersion.verLe ⟨e, rel, .dev n⟩ ⟨e, rel, .post m⟩ = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .dev n⟩ ⟨e, rel, .post m⟩ = false)

/-- `post` is the strictly GREATEST tag. Within a fixed epoch and release a
    `post` release with *any* qualifier number is strictly above `dev`, `a`, `b`,
    `rc`, and the final release — each with an *arbitrary independent* qualifier
    number (`≤` and not order-equal). Pins `post` as the global tag maximum. -/
def spec_tag_final_lt_post (impl : RepoImpl) : Prop :=
  ∀ (e : Nat) (rel : List Nat) (n m : Nat),
    (impl.packagingVersion.verLe ⟨e, rel, .dev m⟩  ⟨e, rel, .post n⟩ = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .dev m⟩  ⟨e, rel, .post n⟩ = false) ∧
    (impl.packagingVersion.verLe ⟨e, rel, .a m⟩    ⟨e, rel, .post n⟩ = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .a m⟩    ⟨e, rel, .post n⟩ = false) ∧
    (impl.packagingVersion.verLe ⟨e, rel, .b m⟩    ⟨e, rel, .post n⟩ = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .b m⟩    ⟨e, rel, .post n⟩ = false) ∧
    (impl.packagingVersion.verLe ⟨e, rel, .rc m⟩   ⟨e, rel, .post n⟩ = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .rc m⟩   ⟨e, rel, .post n⟩ = false) ∧
    (impl.packagingVersion.verLe ⟨e, rel, .none'⟩  ⟨e, rel, .post n⟩ = true ∧
       impl.packagingVersion.verEq ⟨e, rel, .none'⟩  ⟨e, rel, .post n⟩ = false)

-- ── sortVers: structural laws ───────────────────────────────────

/-- `sortVers []` is `[]`. -/
def spec_sort_nil (impl : RepoImpl) : Prop :=
  impl.packagingVersion.sortVers [] = []

/-- `sortVers` preserves length (it neither drops nor duplicates elements). -/
def spec_sort_length (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver), (impl.packagingVersion.sortVers xs).length = xs.length

/-- `sortVers` preserves membership in both directions: `v` is in the sorted
    list iff it was in the input. -/
def spec_sort_mem (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (v : Ver),
    v ∈ impl.packagingVersion.sortVers xs ↔ v ∈ xs

/-- CANONICAL form: `sortVers` is idempotent — sorting an already-sorted list
    leaves it unchanged. A strong canonicality law: it forces the sort output
    to be a genuine fixed point of the ordering, not merely some permutation. -/
def spec_sort_idempotent (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver),
    impl.packagingVersion.sortVers (impl.packagingVersion.sortVers xs)
      = impl.packagingVersion.sortVers xs

-- ── maxVer: boundary + cross-API ────────────────────────────────

/-- `maxVer` returns `none` exactly on the empty list. -/
def spec_max_nil_iff (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver),
    impl.packagingVersion.maxVer xs = none ↔ xs = []

/-- `maxVer` of a singleton is that element. -/
def spec_max_singleton (impl : RepoImpl) : Prop :=
  ∀ (v : Ver), impl.packagingVersion.maxVer [v] = some v

/-- CROSS-API law: `maxVer` agrees with the last element of `sortVers`. Both
    APIs select the same element — the (last-occurring) greatest under `verLe`.
    A strong consistency law tying the argmax and the canonical sort together. -/
def spec_max_eq_sort_last (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver),
    impl.packagingVersion.maxVer xs
      = (impl.packagingVersion.sortVers xs).getLast?

-- ── deep sorting-correctness laws ───────────────────────────────

/-- FULL (not merely adjacent) sortedness: in `sortVers xs` every earlier
    element is `≤` every later element, i.e. `List.Pairwise verLe`. Strictly
    stronger than the adjacent `spec_sort_sorted`: it pins the *global* order of
    the output, ruling out any "sort" that only orders neighbours while leaving
    distant pairs out of order. This is what a caller expects when reading a sorted
    changelog — any version listed earlier is genuinely `≤` every later one. -/
def spec_sort_pairwise_le (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver),
    List.Pairwise (fun a b => impl.packagingVersion.verLe a b = true)
      (impl.packagingVersion.sortVers xs)

/-- MULTIPLICITY preservation: for *any* boolean predicate `p`, the number of
    elements of `sortVers xs` satisfying `p` equals the number in `xs`. A
    counting law stronger than mere membership/length: it forbids a "sort"
    that drops a duplicate or substitutes one element for an equal-count
    sibling. Phrased over an arbitrary `p`, so it pins the full multiset. -/
def spec_sort_count_eq (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (p : Ver → Bool),
    (impl.packagingVersion.sortVers xs).countP p = xs.countP p

/-- The head of `sortVers xs` is the LEAST element: it is `≤` every element of
    the (sorted) output. Mirror of the greatest-element law on the other end of
    the list — the front of the sorted version list is the oldest version, `≤`
    everything after it. -/
def spec_sort_head_le_all (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (h : Ver),
    (impl.packagingVersion.sortVers xs).head? = some h →
      ∀ (z : Ver), z ∈ impl.packagingVersion.sortVers xs →
        impl.packagingVersion.verLe h z = true

/-- CANONICAL-FORM characterisation (bidirectional): `sortVers xs = xs` exactly
    when `xs` is already adjacent-sorted under `verLe`. So `sortVers` leaves a list
    untouched precisely when that list was already in order, and otherwise genuinely
    reorders it. Pins `sortVers` as the canonical representative of each permutation
    class — the unique already-sorted form a caller can test for. -/
def spec_sort_eq_self_iff_sorted (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver),
    impl.packagingVersion.sortVers xs = xs ↔
      Sorted (fun a b => impl.packagingVersion.verLe a b = true) xs

-- ── explicit strictly-increasing transitivity chain ────────────

/-- A concrete eight-version chain spanning every ordering axis (dev/a/final
    pre-tags within a release, intra-release lexicographic growth, epoch jumps)
    is strictly increasing under `verLe` over its full transitive closure. Stated
    as `List.Pairwise`: for *every* `i < j` the earlier version is `≤` the later
    AND not `verEq` — all 28 ordered pairs, not merely the seven adjacent. -/
def spec_chain_strictly_increasing (impl : RepoImpl) : Prop :=
  List.Pairwise
    (fun a b => impl.packagingVersion.verLe a b = true ∧
                impl.packagingVersion.verEq a b = false)
    [ (⟨0, [1], .dev 0⟩ : Ver), ⟨0, [1], .a 0⟩, ⟨0, [1], .none'⟩, ⟨0, [1, 5], .dev 0⟩,
      ⟨0, [2], .rc 1⟩, ⟨0, [2], .post 9⟩, ⟨1, [0], .dev 0⟩, ⟨2, [9, 9], .none'⟩ ]

-- ── minVer: unique least + cross-API ────────────────────────────

/-- `minVer xs = some m` implies `m` is a member of `xs` and is `≤` every
    element of `xs` under `verLe` — a least element — AND `m` is unique up to
    order-equality: any other member `w` that is `≤` every element must be
    order-equal to `m`. Full dual of `spec_max_is_greatest`: the witness +
    least property + uniqueness clause together pin the "oldest version" answer
    to a single order-class, so an impl cannot return a non-least representative. -/
def spec_min_is_least (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (m : Ver),
    impl.packagingVersion.minVer xs = some m →
      (m ∈ xs ∧ ∀ (v : Ver), v ∈ xs → impl.packagingVersion.verLe m v = true) ∧
      (∀ (w : Ver), w ∈ xs →
        (∀ (v : Ver), v ∈ xs → impl.packagingVersion.verLe w v = true) →
          impl.packagingVersion.verEq m w = true)

/-- `minVer xs = none` **iff** `xs = []` — the existence boundary dual to
    `spec_max_nil_iff`. Decisive against a degenerate "always `none`" impl:
    every non-empty list must produce a `some` least element, so the witness +
    least + uniqueness clauses of `spec_min_is_least` cannot be satisfied
    vacuously. -/
def spec_min_nil_iff (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver),
    impl.packagingVersion.minVer xs = none ↔ xs = []

/-- `minVer` of a singleton is that element — dual of `spec_max_singleton`. -/
def spec_min_singleton (impl : RepoImpl) : Prop :=
  ∀ (v : Ver), impl.packagingVersion.minVer [v] = some v

/-- CROSS-API law: `minVer` is order-equal to the *first* element of
    `sortVers`. Both APIs pick a least element of the list, so they agree under
    `verEq`. They need not be the *same* `Ver` value: when several versions are
    order-equal (e.g. `1` and `1.0`), the "smallest version" query and the head
    of the sorted list may land on different representatives of that tied class,
    but the two must compare equal under PEP 440. Ties the two least-element
    APIs together up to order-equality. -/
def spec_min_verEq_sort_head (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (m h : Ver),
    impl.packagingVersion.minVer xs = some m →
    (impl.packagingVersion.sortVers xs).head? = some h →
      impl.packagingVersion.verEq m h = true

/-- CROSS-API extremality: for a non-empty list the least is `≤` the greatest,
    `minVer xs ≤ maxVer xs` — a global sanity law tying `minVer` and `maxVer`
    that an impl reporting a least above its own greatest would violate. -/
def spec_min_le_max (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (lo hi : Ver),
    impl.packagingVersion.minVer xs = some lo →
    impl.packagingVersion.maxVer xs = some hi →
      impl.packagingVersion.verLe lo hi = true

-- ── deep stability / structural sort laws ───────────────────────

/-- STABILITY. For any reference version `r`, the subsequence of `sortVers xs`
    formed by the elements order-equal to `r` is *exactly* the corresponding
    subsequence of `xs` — same elements, same multiplicity, AND same relative
    order. So `sortVers` is a stable sort: it never reorders two versions that
    compare order-equal under `verEq` (e.g. it keeps `1` ahead of `1.0` iff the
    input did). Strictly stronger than `spec_sort_count_eq` (which fixes only the
    multiset): this pins the within-class ordering as well — the property a caller
    relies on when the input order of equal-comparing versions carries meaning. -/
def spec_sort_stable (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (r : Ver),
    (impl.packagingVersion.sortVers xs).filter
        (fun z => impl.packagingVersion.verEq r z)
      = xs.filter (fun z => impl.packagingVersion.verEq r z)

/-- ARGMAX append decomposition. The greatest of a concatenation is recovered
    from the greatest of each part: `maxVer (xs ++ ys)` is `maxVer ys` when `xs`
    has no max, `maxVer xs` when `ys` has none, and otherwise the `verLe`-greater
    of the two side-maxima (breaking a tie towards the `ys` side, matching the
    last-occurrence convention of `maxVer`). A divide-and-conquer law for the
    argmax: the newest version of two combined version sets is the newer of their
    two individual newest versions. Lets a caller compute `maxVer` over partitioned
    inputs and recombine the results. -/
def spec_max_append (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Ver),
    impl.packagingVersion.maxVer (xs ++ ys)
      = (match impl.packagingVersion.maxVer xs, impl.packagingVersion.maxVer ys with
         | none,   m      => m
         | m,      none   => m
         | some a, some b => if impl.packagingVersion.verLe a b then some b else some a)

/-- PRESORT ABSORPTION. Sorting a prefix before concatenating does not change
    the final sort: `sortVers (sortVers xs ++ ys) = sortVers (xs ++ ys)`. A caller
    that has already sorted one block of versions loses nothing by sorting again
    after appending more — the pre-sort of the prefix is absorbed. Note this is
    NOT a mere consequence of permutation-invariance: `sortVers` is a stable sort
    and order-equal-but-distinct versions exist (e.g. `1` and `1.0`), so permuting
    the input *can* change the exact output. -/
def spec_sort_presort_prefix (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Ver),
    impl.packagingVersion.sortVers (impl.packagingVersion.sortVers xs ++ ys)
      = impl.packagingVersion.sortVers (xs ++ ys)

/-- SORT / THRESHOLD-FILTER COMMUTE. Filtering by an upper threshold `p` commutes
    with sorting: `(sortVers xs).filter (· ≤ p) = sortVers (xs.filter (· ≤ p))`.
    Selecting the versions `≤ p` and sorting may be done in either order — a
    caller building a sorted "versions at most `p`" view gets the same list
    whether it filters first or sorts first. Pins the interaction of the ordering
    with an upper version cap. -/
def spec_sort_filter_commute (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (p : Ver),
    (impl.packagingVersion.sortVers xs).filter
        (fun z => impl.packagingVersion.verLe z p)
      = impl.packagingVersion.sortVers
          (xs.filter (fun z => impl.packagingVersion.verLe z p))

/-- ARGMIN append decomposition (dual of `spec_max_append`). The least of a
    concatenation is recovered from the least of each part: empty handling, else
    the `verLe`-lesser of the two side-minima, breaking a tie towards the `ys`
    side (matching the last-occurrence convention of `minVer`). A divide-and-conquer
    law: the oldest version of two combined version sets is the older of their two
    individual oldest versions. Lets a caller compute `minVer` over partitioned
    inputs and recombine the results. -/
def spec_min_append (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Ver),
    impl.packagingVersion.minVer (xs ++ ys)
      = (match impl.packagingVersion.minVer xs, impl.packagingVersion.minVer ys with
         | none,   m      => m
         | m,      none   => m
         | some a, some b => if impl.packagingVersion.verLe b a then some b else some a)

/-- SORT / LOWER-THRESHOLD-FILTER COMMUTE. Filtering by a *lower* threshold `p`
    (keep `p ≤ ·`) commutes with sorting:
    `(sortVers xs).filter (p ≤ ·) = sortVers (xs.filter (p ≤ ·))`. The mirror of
    `spec_sort_filter_commute` on the other end of the order — a caller building a
    sorted "versions at least `p`" view gets the same list whether it filters
    first or sorts first. Pins the interaction of the ordering with a lower version
    floor. -/
def spec_sort_filter_lower_commute (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (p : Ver),
    (impl.packagingVersion.sortVers xs).filter
        (fun z => impl.packagingVersion.verLe p z)
      = impl.packagingVersion.sortVers
          (xs.filter (fun z => impl.packagingVersion.verLe p z))

/-- PRESORT ABSORPTION (suffix). Sorting the *suffix* before concatenating does
    not change the final sort: `sortVers (xs ++ sortVers ys) = sortVers (xs ++ ys)`.
    Companion to `spec_sort_presort_prefix` on the other half: a caller that has
    already sorted the trailing block of versions loses nothing by re-sorting after
    prepending more. The pre-sort of the suffix is absorbed. -/
def spec_sort_presort_suffix (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Ver),
    impl.packagingVersion.sortVers (xs ++ impl.packagingVersion.sortVers ys)
      = impl.packagingVersion.sortVers (xs ++ ys)

/-- PRESORT ABSORPTION (both sides). Pre-sorting *both* halves is absorbed:
    `sortVers (sortVers xs ++ sortVers ys) = sortVers (xs ++ ys)`. A caller that
    merges two independently-sorted version lists and re-sorts the result lands on
    the same list as sorting the raw concatenation. -/
def spec_sort_presort_both (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Ver),
    impl.packagingVersion.sortVers
        (impl.packagingVersion.sortVers xs ++ impl.packagingVersion.sortVers ys)
      = impl.packagingVersion.sortVers (xs ++ ys)

/-- ARGMAX is SORT-INVARIANT: `maxVer (sortVers xs) = maxVer xs`. Sorting first
    does not change the greatest, down to the exact `Ver` value returned
    (including the last-occurrence tie-break among order-equal maxima). Pre-sorting
    a version list before asking for its newest element is a no-op — a consistency
    guarantee a caller relies on when caching a sorted view. -/
def spec_max_sort_invariant (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver),
    impl.packagingVersion.maxVer (impl.packagingVersion.sortVers xs)
      = impl.packagingVersion.maxVer xs

/-- ARGMIN is SORT-INVARIANT (dual): `minVer (sortVers xs) = minVer xs`. Sorting
    first does not change the least, down to the exact `Ver` value returned.
    Pre-sorting a version list before asking for its oldest element is a no-op —
    the consistency mirror of `spec_max_sort_invariant`. -/
def spec_min_sort_invariant (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver),
    impl.packagingVersion.minVer (impl.packagingVersion.sortVers xs)
      = impl.packagingVersion.minVer xs

/-- ARGMAX is CONCATENATION-ORDER-INDEPENDENT up to `verEq`: the greatest of
    `xs ++ ys` is order-equal to the greatest of `ys ++ xs`
    (`maxVer (xs ++ ys) ~ maxVer (ys ++ xs)`), stated as both `none` together or
    both `some` with `verEq`. The *exact* values can differ — the last-occurrence
    tie-break is position-sensitive, so swapping the two blocks may return a
    different representative of a tied-greatest class — hence the law holds only up
    to `verEq`. The newest version of a combined set does not depend on which
    block was listed first. -/
def spec_max_concat_comm_verEq (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Ver),
    (impl.packagingVersion.maxVer (xs ++ ys) = none ∧
       impl.packagingVersion.maxVer (ys ++ xs) = none) ∨
    (∃ a b, impl.packagingVersion.maxVer (xs ++ ys) = some a ∧
            impl.packagingVersion.maxVer (ys ++ xs) = some b ∧
            impl.packagingVersion.verEq a b = true)

/-- ARGMIN is CONCATENATION-ORDER-INDEPENDENT up to `verEq` (dual of
    `spec_max_concat_comm_verEq`): `minVer (xs ++ ys) ~ minVer (ys ++ xs)`. The
    exact values can differ (the position-sensitive last-occurrence tie-break may
    return a different representative of a tied-least class when the blocks swap),
    so the law holds only up to `verEq`. The oldest version of a combined set does
    not depend on which block was listed first. -/
def spec_min_concat_comm_verEq (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Ver),
    (impl.packagingVersion.minVer (xs ++ ys) = none ∧
       impl.packagingVersion.minVer (ys ++ xs) = none) ∨
    (∃ a b, impl.packagingVersion.minVer (xs ++ ys) = some a ∧
            impl.packagingVersion.minVer (ys ++ xs) = some b ∧
            impl.packagingVersion.verEq a b = true)

-- ── interval filter / extremal-query commutation ──

/-- SORT / INTERVAL-FILTER COMMUTE. A two-sided filter — keep the versions in the
    closed band `lo ≤ · ≤ hi` — commutes with sorting:
    `(sortVers xs).filter (lo ≤ · ≤ hi) = sortVers (xs.filter (lo ≤ · ≤ hi))`.
    A caller building a sorted "versions between `lo` and `hi`" view gets the same
    list whether it filters first or sorts first. -/
def spec_sort_filter_interval_commute (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (lo hi : Ver),
    (impl.packagingVersion.sortVers xs).filter
        (fun z => impl.packagingVersion.verLe lo z && impl.packagingVersion.verLe z hi)
      = impl.packagingVersion.sortVers
          (xs.filter (fun z => impl.packagingVersion.verLe lo z && impl.packagingVersion.verLe z hi))

/-- CAPPED ARGMAX is SORT-INVARIANT. The greatest version `≤ p` present in `xs`
    is the same whether computed from the raw list or from a cached sorted view:
    `maxVer ((sortVers xs).filter (· ≤ p)) = maxVer (xs.filter (· ≤ p))`. Lets a
    caller answer every "newest version at most `p`" query against one sorted
    view. -/
def spec_max_filter_below_commute (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (p : Ver),
    impl.packagingVersion.maxVer
        ((impl.packagingVersion.sortVers xs).filter (fun z => impl.packagingVersion.verLe z p))
      = impl.packagingVersion.maxVer
          (xs.filter (fun z => impl.packagingVersion.verLe z p))

/-- CAPPED ARGMIN is SORT-INVARIANT (dual). The least version `≥ p` present in
    `xs` is the same from the raw list or from a cached sorted view:
    `minVer ((sortVers xs).filter (p ≤ ·)) = minVer (xs.filter (p ≤ ·))`. The
    mirror of `spec_max_filter_below_commute` on the floor side. -/
def spec_min_filter_above_commute (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (p : Ver),
    impl.packagingVersion.minVer
        ((impl.packagingVersion.sortVers xs).filter (fun z => impl.packagingVersion.verLe p z))
      = impl.packagingVersion.minVer
          (xs.filter (fun z => impl.packagingVersion.verLe p z))

/-- CAPPED SORTED VIEW is a CANONICAL FIXED POINT. Re-sorting a capped slice of an
    already-sorted list changes nothing:
    `sortVers ((sortVers xs).filter (· ≤ p)) = (sortVers xs).filter (· ≤ p)`.
    Pins each capped view as the unique already-sorted representative a caller can
    test for. -/
def spec_filter_below_sorted_fixed (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (p : Ver),
    impl.packagingVersion.sortVers
        ((impl.packagingVersion.sortVers xs).filter (fun z => impl.packagingVersion.verLe z p))
      = (impl.packagingVersion.sortVers xs).filter (fun z => impl.packagingVersion.verLe z p)

/-- PRESORT ABSORPTION (middle segment). Sorting a MIDDLE block before splicing it
    between a prefix and a suffix does not change the final sort:
    `sortVers (xs ++ sortVers ys ++ zs) = sortVers (xs ++ ys ++ zs)`. Generalises
    the prefix/suffix/both absorption laws to an arbitrary interior segment — a
    caller that keeps one block of a version list pre-sorted loses nothing by
    re-sorting after splicing it into any position. Like the prefix/suffix laws
    this is NOT a consequence of permutation-invariance (the stable sort is
    position-sensitive on order-equal-but-distinct versions such as `1` and
    `1.0`). -/
def spec_sort_presort_middle (impl : RepoImpl) : Prop :=
  ∀ (xs ys zs : List Ver),
    impl.packagingVersion.sortVers
        (xs ++ impl.packagingVersion.sortVers ys ++ zs)
      = impl.packagingVersion.sortVers (xs ++ ys ++ zs)

/-- INDEX MONOTONICITY. Looking up two positions in a sorted version list respects
    the index order: any element at an earlier index is `≤` any element at a
    later index. -/
def spec_sort_index_monotone (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (i j : Nat) (a b : Ver),
    i ≤ j →
    (impl.packagingVersion.sortVers xs)[i]? = some a →
    (impl.packagingVersion.sortVers xs)[j]? = some b →
      impl.packagingVersion.verLe a b = true

/-- TWO-INDEX STABILITY. If two order-equal versions occur in the input at
    strictly increasing indices, then the sorted output contains the same two
    concrete versions in strictly increasing index order. -/
def spec_sort_stable_two_index (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (i j : Nat) (a b : Ver),
    i < j →
    xs[i]? = some a → xs[j]? = some b →
    impl.packagingVersion.verEq a b = true →
      ∃ i' j' : Nat, i' < j' ∧
        (impl.packagingVersion.sortVers xs)[i']? = some a ∧
        (impl.packagingVersion.sortVers xs)[j']? = some b

/-- STABLE SORTED-PERMUTATION UNIQUENESS. A sorted permutation of `xs` whose
    every `verEq`-class subsequence matches `xs` is exactly `sortVers xs`. -/
def spec_sort_eq_of_sorted_stable_perm (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Ver),
    ys.Perm xs →
    List.Pairwise (fun a b => impl.packagingVersion.verLe a b = true) ys →
    (∀ (r : Ver),
      ys.filter (fun z => impl.packagingVersion.verEq r z)
        = xs.filter (fun z => impl.packagingVersion.verEq r z)) →
      impl.packagingVersion.sortVers xs = ys

/-- Alternating merge used by the interleave sort law. -/
def interleaveVers : List Ver → List Ver → List Ver
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => x :: y :: interleaveVers xs ys

/-- DISJOINT INTERLEAVE SORT EQUALITY. If no version in `xs` is order-equal to
    any version in `ys`, sorting an alternating interleave is the same as sorting
    the append. -/
def spec_sort_interleave_disjoint_eq_append (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Ver),
    (∀ (x : Ver), x ∈ xs → ∀ (y : Ver), y ∈ ys →
      impl.packagingVersion.verEq x y = false) →
      impl.packagingVersion.sortVers (interleaveVers xs ys)
        = impl.packagingVersion.sortVers (xs ++ ys)

-- ── canonical-form / lex-tower / order-statistic layer ──────────

/-- Spec-side strict-order helper: `a` is below `b` and not order-equal. -/
def strictBelow (impl : RepoImpl) (a b : Ver) : Bool :=
  impl.packagingVersion.verLe a b && (!(impl.packagingVersion.verEq a b))

/-- Spec-side release normalizer: drop the maximal run of trailing zeros. -/
def releaseNorm (r : List Nat) : List Nat :=
  (r.reverse.dropWhile (fun n => n == 0)).reverse

/-- Normalize a version's release tuple by `releaseNorm`. -/
def normVer (v : Ver) : Ver := { v with release := releaseNorm v.release }

/-- Spec-side insertion under a `verLe`: place `x` before the first `y` it is
    `verLe` to, else keep scanning (the stable-sort insertion step). -/
def insertByLe (impl : RepoImpl) (x : Ver) : List Ver → List Ver
  | []      => [x]
  | y :: ys =>
      if impl.packagingVersion.verLe x y then x :: y :: ys
      else y :: insertByLe impl x ys

/-- Spec-side fuel-bounded stable merge of two lists under `verLe`, taking the
    left element on a tie. -/
def mergeFuel (impl : RepoImpl) : Nat → List Ver → List Ver → List Ver
  | 0,     xs,      ys      => xs ++ ys
  | _ + 1, [],      ys      => ys
  | _ + 1, xs,      []      => xs
  | n + 1, x :: xs, y :: ys =>
      if impl.packagingVersion.verLe x y then x :: mergeFuel impl n xs (y :: ys)
      else y :: mergeFuel impl n (x :: xs) ys

/-- Spec-side stable merge with fuel `length xs + length ys`. -/
def mergeVers (impl : RepoImpl) (xs ys : List Ver) : List Ver :=
  mergeFuel impl (xs.length + ys.length) xs ys

/-- CANONICAL NORMAL FORM of order-equality: `verEq a b` holds iff the two
    versions agree on all three frozen axes — the epoch is equal, the releases
    compare `eq` under the trailing-zero-trimmed `relCmp`, and the tags compare
    `eq` under `tagCmp`. A complete invariant of the `verEq` class, phrased over
    the frozen comparison vocabulary. -/
def spec_eq_iff_frozen_axes (impl : RepoImpl) : Prop :=
  ∀ (a b : Ver),
    impl.packagingVersion.verEq a b = true ↔
      a.epoch = b.epoch ∧
      relCmp a.release b.release = Ordering.eq ∧
      tagCmp a.pre b.pre = Ordering.eq

/-- ORDER TRICHOTOMY: any two versions fall into exactly one of three states —
    strictly below (`verLe a b`, not `verEq`, and `¬ verLe b a`), order-equal
    (both `verLe` and `verEq`), or strictly above (`¬ verLe a b`, not `verEq`,
    and `verLe b a`). Pins `verLe`/`verEq` as a genuine total order with a single
    equality class per tie. -/
def spec_full_order_trichotomy (impl : RepoImpl) : Prop :=
  ∀ (a b : Ver),
    (impl.packagingVersion.verLe a b = true ∧
     impl.packagingVersion.verEq a b = false ∧
     impl.packagingVersion.verLe b a = false) ∨
    (impl.packagingVersion.verLe a b = true ∧
     impl.packagingVersion.verEq a b = true ∧
     impl.packagingVersion.verLe b a = true) ∨
    (impl.packagingVersion.verLe a b = false ∧
     impl.packagingVersion.verEq a b = false ∧
     impl.packagingVersion.verLe b a = true)

/-- LEX-TOWER characterisation of `verLe`: `verLe a b` holds iff the epoch is
    strictly smaller, or the epochs tie and `relCmp` is `lt`, or the epochs tie
    and `relCmp` is `eq` and the tag comparison `tagCmp` is not `gt`. Pins the
    full epoch > release > tag lexicographic order. -/
def spec_le_iff_lex_axes (impl : RepoImpl) : Prop :=
  ∀ (a b : Ver),
    impl.packagingVersion.verLe a b = true ↔
      a.epoch < b.epoch ∨
      (a.epoch = b.epoch ∧ relCmp a.release b.release = Ordering.lt) ∨
      (a.epoch = b.epoch ∧ relCmp a.release b.release = Ordering.eq ∧
        tagCmp a.pre b.pre ≠ Ordering.gt)

/-- RELEASE NORMAL-FORM transparency: each release compares `eq` under `relCmp`
    with its trailing-zero-stripped form, and replacing both operands' releases
    by that stripped form leaves both `verLe` and `verEq` unchanged. Trailing
    zeros are order-transparent everywhere, and the stripped release is a
    canonical representative of the release axis. -/
def spec_release_normal_form_invariant (impl : RepoImpl) : Prop :=
  ∀ (a b : Ver),
    relCmp a.release (releaseNorm a.release) = Ordering.eq ∧
    relCmp b.release (releaseNorm b.release) = Ordering.eq ∧
    impl.packagingVersion.verLe a b =
      impl.packagingVersion.verLe (normVer a) (normVer b) ∧
    impl.packagingVersion.verEq a b =
      impl.packagingVersion.verEq (normVer a) (normVer b)

/-- STRICT-PREFIX COUNT: in `sortVers xs`, the elements strictly below any
    `pivot` occupy exactly the initial segment of length `n`, where `n` is the
    number of strictly-below elements in `xs`; the remaining suffix contains no
    strictly-below element. Ties the strict-below count of the input to the exact
    prefix boundary of the sorted output. -/
def spec_sort_strict_prefix_count (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (pivot : Ver),
    let n := xs.countP (fun z => strictBelow impl z pivot)
    ((impl.packagingVersion.sortVers xs).take n).all
        (fun z => strictBelow impl z pivot) = true ∧
    ((impl.packagingVersion.sortVers xs).drop n).all
        (fun z => !(strictBelow impl z pivot)) = true

/-- EQUALITY-CLASS BLOCK: the members of any `pivot`'s order-equality class form
    one contiguous block in `sortVers xs`, starting right after all strictly-lower
    elements, and appearing in their original input order. Concretely the slice
    `(sortVers xs).drop lo |>.take eqn` (with `lo` the strict-below count and
    `eqn` the class size) equals `xs.filter (verEq pivot ·)`. -/
def spec_sort_eq_class_block (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (pivot : Ver),
    let lo := xs.countP (fun z => strictBelow impl z pivot)
    let eqn := xs.countP (fun z => impl.packagingVersion.verEq pivot z)
    ((impl.packagingVersion.sortVers xs).drop lo).take eqn =
      xs.filter (fun z => impl.packagingVersion.verEq pivot z)

/-- ORDER-STATISTIC BAND: the sorted index `i` of any element `v` lies at or
    after the number of elements strictly below `v`, and strictly before the
    number of elements `≤ v`. So an element's sorted position is bounded by its
    input rank statistics. -/
def spec_order_statistic_band (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (i : Nat) (v : Ver),
    (impl.packagingVersion.sortVers xs)[i]? = some v →
      xs.countP (fun z => strictBelow impl z v) ≤ i ∧
      i < xs.countP (fun z => impl.packagingVersion.verLe z v)

/-- EQUALITY-CLASS CONVEXITY: in `sortVers xs`, if two positions `i ≤ k` both
    hold members of a reference version `r`'s order-equality class, then every
    position `j` between them also holds a member of that class. Each `verEq`
    class occupies a contiguous (convex) index range in the sorted output. -/
def spec_sort_verEq_class_convex (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (r : Ver) (i j k : Nat) (a b c : Ver),
    i ≤ j → j ≤ k →
    (impl.packagingVersion.sortVers xs)[i]? = some a →
    (impl.packagingVersion.sortVers xs)[j]? = some b →
    (impl.packagingVersion.sortVers xs)[k]? = some c →
    impl.packagingVersion.verEq r a = true →
    impl.packagingVersion.verEq r c = true →
      impl.packagingVersion.verEq r b = true

/-- CONS / INSERTION law: `sortVers (x :: xs)` equals inserting `x` into
    `sortVers xs` at its stable rank (`insertByLe`). Ties the whole-list sort to
    the single-element insertion step. -/
def spec_sort_cons_insert_rank (impl : RepoImpl) : Prop :=
  ∀ (x : Ver) (xs : List Ver),
    impl.packagingVersion.sortVers (x :: xs)
      = insertByLe impl x (impl.packagingVersion.sortVers xs)

/-- APPEND / FOLD-FUSION law: `sortVers (xs ++ ys)` equals folding the stable
    insertion of each element of `xs` (right to left) over the already-sorted
    `sortVers ys`. A caller with a pre-sorted suffix incorporates a new prefix
    element-by-element. -/
def spec_sort_append_fold_insert (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Ver),
    impl.packagingVersion.sortVers (xs ++ ys)
      = xs.foldr (fun x acc => insertByLe impl x acc)
          (impl.packagingVersion.sortVers ys)

/-- APPEND / STABLE-MERGE law: `sortVers (xs ++ ys)` equals the stable merge of
    the two independently sorted halves (`mergeVers`, taking the left element on
    a tie). Stronger than presort absorption: it pins the exact interleaving of
    two sorted version lists, tie-representatives included. -/
def spec_sort_append_stable_merge (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Ver),
    impl.packagingVersion.sortVers (xs ++ ys)
      = mergeVers impl
          (impl.packagingVersion.sortVers xs)
          (impl.packagingVersion.sortVers ys)

/-- EXTREMA are PERMUTATION-INVARIANT up to `verEq`: for any permutation `ys` of
    `xs`, the least versions agree under `verEq` and the greatest versions agree
    under `verEq`. Reordering the input never changes which order-class is least
    or greatest, even though the exact tie representative may differ. -/
def spec_extrema_perm_unique_classes (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Ver) (lo1 lo2 hi1 hi2 : Ver),
    ys.Perm xs →
    impl.packagingVersion.minVer xs = some lo1 →
    impl.packagingVersion.minVer ys = some lo2 →
    impl.packagingVersion.maxVer xs = some hi1 →
    impl.packagingVersion.maxVer ys = some hi2 →
      impl.packagingVersion.verEq lo1 lo2 = true ∧
      impl.packagingVersion.verEq hi1 hi2 = true

/-- MAX SURVIVES a FLOOR FILTER: if `maxVer xs = some m` and a floor `p` is `≤ m`,
    then filtering `xs` to the versions `≥ p` still returns exactly `m` as the
    greatest — the exact tie representative is preserved. Filtering out versions
    below a floor cannot disturb the reported newest version when it clears the
    floor. -/
def spec_max_filter_above_keeps_top (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver) (p m : Ver),
    impl.packagingVersion.maxVer xs = some m →
    impl.packagingVersion.verLe p m = true →
      impl.packagingVersion.maxVer
        (xs.filter (fun z => impl.packagingVersion.verLe p z)) = some m

/-- ADJACENT-STRICT ⇒ FULLY-STRICT chain: any list whose adjacent pairs are all
    strictly increasing under `verLe` (and not `verEq`) is strictly increasing
    over its full transitive closure (`List.Pairwise`). Every earlier version is
    strictly below every later one, not merely its neighbour. -/
def spec_strict_chain_pairwise_from_adjacent (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver),
    Sorted (fun a b => impl.packagingVersion.verLe a b = true ∧
                       impl.packagingVersion.verEq a b = false) xs →
      List.Pairwise (fun a b => impl.packagingVersion.verLe a b = true ∧
                                impl.packagingVersion.verEq a b = false) xs

/-- NO-DUPLICATE-CLASS ⇒ GLOBALLY STRICT sort: if no two elements of `xs` are
    order-equal, then `sortVers xs` is strictly increasing over every ordered
    pair (`List.Pairwise` of `verLe` and not `verEq`). Sorting a set of pairwise
    distinct-class versions yields a genuine strict chain. -/
def spec_sort_class_nodup_pairwise_strict (impl : RepoImpl) : Prop :=
  ∀ (xs : List Ver),
    List.Pairwise (fun a b => impl.packagingVersion.verEq a b = false) xs →
      List.Pairwise (fun a b => impl.packagingVersion.verLe a b = true ∧
                                impl.packagingVersion.verEq a b = false)
        (impl.packagingVersion.sortVers xs)

end PackagingVersion.Spec
