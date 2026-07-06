import Semver.Harness

/-!
# Semver.Spec.Version

Specifications for the SemVer 2.0.0 precedence + constraint-selection
operations. Each `spec_*` is a property over an arbitrary `impl : RepoImpl`;
the API is always reached through `impl.semver.<fn>`, never by calling the
reference `Semver.<fn>` directly.

The specs pin the intended SemVer 2.0.0 order without copying the reference
comparator body:

* the total-order axioms (totality, reflexivity, antisymmetry, transitivity,
  trichotomy) plus `eq` as an equivalence;
* the field-precedence laws fixing `major > minor > patch` as the dominant axes
  and reducing core ties to the pre-release comparison;
* the SemVer discriminators — a pre-release lowers precedence, build metadata is
  invisible, numeric identifiers rank below alphanumeric ones, longer
  pre-releases rank higher;
* `select` pinned as the greatest matching version by witness, maximality,
  uniqueness (up to `eq`), the empty-result dual, and invariance under
  reordering and pruning non-matches.

Field comparisons are phrased through the frozen `preFieldCmpRef` /
`preCmpRef` / `identCmpRef` relations, so they anchor to shared vocabulary rather
than copy an oracle comparator.

The `…Ref` relations below are the specification's OWN frozen pre-release
comparison vocabulary — they are the fixed, shared field-precedence primitives
the specs refer to, NOT part of the implementation the agent must write. They are
defined here (outside every `!benchmark` marker, so always shipped) so the specs
are self-contained: the pre-release comparison the specs anchor to does not
depend on any implementation helper. A conforming implementation must satisfy the
specs stated through them (the reference implementation keeps its own definitionally
identical copies inside `Impl/Version.lean`).
-/

-- ── frozen pre-release comparison vocabulary (SPEC-SIDE, always shipped) ──

/-- Three-way comparison of a single pre-release identifier (frozen spec-side
    vocabulary). SemVer §11.4: numeric identifiers always rank below alphanumeric
    identifiers; two numeric identifiers compare numerically; two alphanumeric
    identifiers compare in ASCII order. -/
def identCmpRef : Ident → Ident → Ordering
  | .num a,   .num b   => compare a b
  | .num _,   .alpha _ => .lt
  | .alpha _, .num _   => .gt
  | .alpha a, .alpha b => compare a b

/-- Three-way comparison of pre-release identifier lists (frozen spec-side
    vocabulary), SemVer §11.4: the ordinary identifier-list order in which, among
    lists sharing a prefix, the longer one ranks higher (§11.4.4). The special
    "empty pre-release is GREATEST" rule lives in `preFieldCmpRef`, not here. -/
def preCmpRef : List Ident → List Ident → Ordering
  | [],      []      => .eq
  | [],      _ :: _  => .lt          -- fewer identifiers ranks below more
  | _ :: _,  []      => .gt
  | x :: xs, y :: ys => match identCmpRef x y with
                        | .eq => preCmpRef xs ys
                        | o   => o

/-- Three-way comparison of the pre-release FIELD (frozen spec-side vocabulary).
    SemVer §11.3: a version WITHOUT a pre-release (the empty list) has the
    GREATEST precedence, so the empty list ranks above any non-empty one; two
    non-empty lists are compared by `preCmpRef`. -/
def preFieldCmpRef : List Ident → List Ident → Ordering
  | [],      []      => .eq
  | [],      _ :: _  => .gt          -- no pre-release ranks above a pre-release
  | _ :: _,  []      => .lt
  | x :: xs, y :: ys => preCmpRef (x :: xs) (y :: ys)

namespace Semver.Spec

-- ── total-order axioms (compareV / lt / eq) ────────────────────

/-- `compareV` is total: it never fails to decide, and swapping the arguments
    swaps the result (`compareV b a = (compareV a b).swap`). Pins `compareV` as
    a genuine three-way comparison, antisymmetric by construction. -/
def spec_compare_swap (impl : RepoImpl) : Prop :=
  ∀ (a b : Version),
    impl.semver.compareV b a = (impl.semver.compareV a b).swap

/-- Reflexivity: a version compares `.eq` with itself. -/
def spec_compare_refl (impl : RepoImpl) : Prop :=
  ∀ (a : Version), impl.semver.compareV a a = Ordering.eq

/-- TRANSITIVITY of the underlying order, phrased on `compareV`: if `a ≤ b` and
    `b ≤ c` (neither comparison is `.gt`) then `a ≤ c`. -/
def spec_compare_trans (impl : RepoImpl) : Prop :=
  ∀ (a b c : Version),
    impl.semver.compareV a b ≠ Ordering.gt →
    impl.semver.compareV b c ≠ Ordering.gt →
    impl.semver.compareV a c ≠ Ordering.gt

/-- `lt` is exactly `compareV = .lt`, and `eq` is exactly `compareV = .eq`:
    the two boolean APIs are the strict-less and equal projections of the same
    three-way comparator. Ties `lt`/`eq` to `compareV` without copying the
    comparator body. -/
def spec_lt_eq_compare (impl : RepoImpl) : Prop :=
  ∀ (a b : Version),
    (impl.semver.versionLt a b = true ↔ impl.semver.compareV a b = Ordering.lt) ∧
    (impl.semver.versionEq a b = true ↔ impl.semver.compareV a b = Ordering.eq)

/-- TRICHOTOMY: for any two versions exactly one of `lt a b`, `eq a b`,
    `lt b a` holds. Stated positively (at least one) and exclusively (no two
    together), forcing `lt`/`eq` to partition every pair. -/
def spec_trichotomy (impl : RepoImpl) : Prop :=
  ∀ (a b : Version),
    (impl.semver.versionLt a b = true ∨ impl.semver.versionEq a b = true ∨ impl.semver.versionLt b a = true) ∧
    ¬ (impl.semver.versionLt a b = true ∧ impl.semver.versionEq a b = true) ∧
    ¬ (impl.semver.versionLt a b = true ∧ impl.semver.versionLt b a = true) ∧
    ¬ (impl.semver.versionEq a b = true ∧ impl.semver.versionLt b a = true)

/-- `lt` is IRREFLEXIVE: a version is never strictly less than itself. -/
def spec_lt_irrefl (impl : RepoImpl) : Prop :=
  ∀ (a : Version), impl.semver.versionLt a a = false

/-- `lt` is TRANSITIVE. -/
def spec_lt_trans (impl : RepoImpl) : Prop :=
  ∀ (a b c : Version),
    impl.semver.versionLt a b = true →
    impl.semver.versionLt b c = true →
    impl.semver.versionLt a c = true

-- ── eq is an equivalence ───────────────────────────────────────

/-- `eq` is reflexive. -/
def spec_eq_refl (impl : RepoImpl) : Prop :=
  ∀ (a : Version), impl.semver.versionEq a a = true

/-- `eq` is symmetric. -/
def spec_eq_symm (impl : RepoImpl) : Prop :=
  ∀ (a b : Version),
    impl.semver.versionEq a b = true → impl.semver.versionEq b a = true

/-- `eq` is transitive. -/
def spec_eq_trans (impl : RepoImpl) : Prop :=
  ∀ (a b c : Version),
    impl.semver.versionEq a b = true →
    impl.semver.versionEq b c = true →
    impl.semver.versionEq a c = true

-- ── field-precedence laws (major > minor > patch) ──────────────

/-- CROSS-AXIS priority: `major` strictly dominates. A strictly greater `major`
    makes a version strictly greater regardless of every other field (minor,
    patch, pre-release, build): if `a.major < b.major` then `lt a b` and `¬ eq`.
    SemVer §11.2. -/
def spec_major_dominates (impl : RepoImpl) : Prop :=
  ∀ (a b : Version),
    a.major < b.major →
      impl.semver.versionLt a b = true ∧ impl.semver.versionEq a b = false

/-- CROSS-AXIS priority: within an equal `major`, a strictly greater `minor`
    strictly dominates `patch` / pre-release / build. -/
def spec_minor_dominates (impl : RepoImpl) : Prop :=
  ∀ (a b : Version),
    a.major = b.major → a.minor < b.minor →
      impl.semver.versionLt a b = true ∧ impl.semver.versionEq a b = false

/-- CROSS-AXIS priority: within equal `major.minor`, a strictly greater `patch`
    strictly dominates the pre-release / build axes. Together with
    `spec_major_dominates` / `spec_minor_dominates` this fixes the lexicographic
    axis order `major > minor > patch > pre-release`. -/
def spec_patch_dominates (impl : RepoImpl) : Prop :=
  ∀ (a b : Version),
    a.major = b.major → a.minor = b.minor → a.patch < b.patch →
      impl.semver.versionLt a b = true ∧ impl.semver.versionEq a b = false

/-- When the whole `major.minor.patch` core ties, the precedence reduces to the
    frozen `preFieldCmpRef` pre-release comparison: `compareV` of two versions
    sharing a core equals `preFieldCmpRef` of their pre-release lists, regardless of
    build. Pins the pre-release list as the least-significant precedence axis,
    phrased through the frozen `preFieldCmpRef` (which encodes both the SemVer
    "empty pre-release is greatest" rule and the identifier-list comparison), so
    it is a frozen-op anchor, not an oracle copy. -/
def spec_core_eq_reduces_to_pre (impl : RepoImpl) : Prop :=
  ∀ (mj mn pa : Nat) (p q : List Ident) (b1 b2 : List String),
    impl.semver.compareV ⟨mj, mn, pa, p, b1⟩ ⟨mj, mn, pa, q, b2⟩ = preFieldCmpRef p q

-- ── pre-release discriminators (LOAD-BEARING) ──────────────────

/-- SemVer §11.3. A version WITH a pre-release has strictly LOWER precedence
    than the same `major.minor.patch` WITHOUT one: for any non-empty pre-release
    list `p`, `⟨c, p, _⟩ < ⟨c, [], _⟩` strictly, so the empty pre-release (a
    normal release) is GREATEST. Stated over arbitrary build metadata. -/
def spec_prerelease_lowers (impl : RepoImpl) : Prop :=
  ∀ (mj mn pa : Nat) (p : List Ident) (b1 b2 : List String),
    p ≠ [] →
      impl.semver.versionLt ⟨mj, mn, pa, p, b1⟩ ⟨mj, mn, pa, [], b2⟩ = true ∧
      impl.semver.versionEq ⟨mj, mn, pa, p, b1⟩ ⟨mj, mn, pa, [], b2⟩ = false

/-- SemVer §11.4.3. Among pre-release identifiers a purely numeric identifier
    has strictly LOWER precedence than an alphanumeric one: sharing a common
    pre-release prefix `p`, the version whose next identifier is numeric is
    strictly below the one whose next identifier is alphanumeric. -/
def spec_pre_numeric_below_alpha (impl : RepoImpl) : Prop :=
  ∀ (mj mn pa : Nat) (p : List Ident) (n : Nat) (s : String) (b1 b2 : List String),
    impl.semver.versionLt ⟨mj, mn, pa, p ++ [.num n], b1⟩ ⟨mj, mn, pa, p ++ [.alpha s], b2⟩ = true ∧
    impl.semver.versionEq ⟨mj, mn, pa, p ++ [.num n], b1⟩ ⟨mj, mn, pa, p ++ [.alpha s], b2⟩ = false

/-- A larger set of pre-release fields has higher precedence when all of the
    preceding identifiers are equal (SemVer §11.4.4), in its GENERAL prefix form:
    sharing a NON-EMPTY pre-release prefix `p`, appending ANY non-empty suffix `q`
    yields a strictly greater version — `⟨…, p, _⟩ < ⟨…, p ++ q, _⟩` for every
    `q ≠ []`, not merely a single trailing identifier. (Both still rank below a
    normal release.) The two `≠ []` guards are essential: with `p = []` the left
    side would be a normal release, which by §11.3 is GREATEST, so the "longer
    wins" rule applies only among genuine pre-releases; with `q = []` the two
    sides coincide. -/
def spec_pre_longer_greater (impl : RepoImpl) : Prop :=
  ∀ (mj mn pa : Nat) (p q : List Ident) (b1 b2 : List String),
    p ≠ [] → q ≠ [] →
      impl.semver.versionLt ⟨mj, mn, pa, p, b1⟩ ⟨mj, mn, pa, p ++ q, b2⟩ = true ∧
      impl.semver.versionEq ⟨mj, mn, pa, p, b1⟩ ⟨mj, mn, pa, p ++ q, b2⟩ = false

-- ── build-metadata discriminator (LOAD-BEARING) ────────────────

/-- SemVer §10. Build metadata is ENTIRELY invisible to
    precedence: changing only the build list leaves `compareV` against an
    arbitrary third version `w` unchanged in BOTH directions, and the two
    build-only variants compare `eq`. This is full order-transparency of build
    metadata, ruling out any order that lets the `+build` suffix break a tie. -/
def spec_build_ignored (impl : RepoImpl) : Prop :=
  ∀ (mj mn pa : Nat) (p : List Ident) (b1 b2 : List String) (w : Version),
    impl.semver.versionEq ⟨mj, mn, pa, p, b1⟩ ⟨mj, mn, pa, p, b2⟩ = true ∧
    impl.semver.compareV ⟨mj, mn, pa, p, b1⟩ w
      = impl.semver.compareV ⟨mj, mn, pa, p, b2⟩ w ∧
    impl.semver.compareV w ⟨mj, mn, pa, p, b1⟩
      = impl.semver.compareV w ⟨mj, mn, pa, p, b2⟩

/-- `eq` pins ALL precedence axes (and only those): two versions are `eq` iff
    they agree on `major`, `minor`, `patch`, AND their pre-release lists compare
    `.eq` under the frozen `preFieldCmpRef` — with NO constraint on build metadata.
    So `eq` identifies exactly the versions differing only in build metadata.
    Phrased through the frozen `preFieldCmpRef`, so it is a frozen-op anchor. -/
def spec_eq_characterisation (impl : RepoImpl) : Prop :=
  ∀ (a b : Version),
    impl.semver.versionEq a b = true ↔
      (a.major = b.major ∧ a.minor = b.minor ∧ a.patch = b.patch ∧
       preFieldCmpRef a.pre b.pre = Ordering.eq)

-- ── explicit strictly-increasing precedence chain ──────────────

/-- A concrete chain spanning every precedence axis is STRICTLY increasing
    under `lt` over its FULL transitive closure (`List.Pairwise`): a numeric
    pre-release below an alphanumeric one, a longer pre-release above a shorter,
    a pre-release below its normal release, and patch/minor/major jumps — for
    *every* `i < j` the earlier is `lt` the later. The SemVer 2.0.0 §11 example
    chain `1.0.0-alpha < 1.0.0-alpha.1 < 1.0.0-alpha.beta < 1.0.0-beta <
    1.0.0-beta.2 < 1.0.0-beta.11 < 1.0.0-rc.1 < 1.0.0 < 1.0.1 < 1.1.0 < 2.0.0`. -/
def spec_semver_chain_strict (impl : RepoImpl) : Prop :=
  List.Pairwise
    (fun a b => impl.semver.versionLt a b = true)
    [ (⟨1, 0, 0, [.alpha "alpha"], []⟩ : Version),
      ⟨1, 0, 0, [.alpha "alpha", .num 1], []⟩,
      ⟨1, 0, 0, [.alpha "alpha", .alpha "beta"], []⟩,
      ⟨1, 0, 0, [.alpha "beta"], []⟩,
      ⟨1, 0, 0, [.alpha "beta", .num 2], []⟩,
      ⟨1, 0, 0, [.alpha "beta", .num 11], []⟩,
      ⟨1, 0, 0, [.alpha "rc", .num 1], []⟩,
      ⟨1, 0, 0, [], []⟩,
      ⟨1, 0, 1, [], []⟩,
      ⟨1, 1, 0, [], []⟩,
      ⟨2, 0, 0, [], []⟩ ]

-- ── satisfies: clause semantics ────────────────────────────────

/-- `satisfies` of the empty constraint is vacuously true (no clause to fail). -/
def spec_satisfies_nil (impl : RepoImpl) : Prop :=
  ∀ (v : Version), impl.semver.satisfies [] v = true

/-- A `≥ lo` constraint is satisfied EXACTLY by the versions that are not
    strictly below `lo`: `satisfies [⟨.ge, lo⟩] v` iff `¬ (v < lo)`. Pins the
    `.ge` clause to the frozen strict order via `lt`, the guarantee a caller
    needs from a lower-bound constraint. -/
def spec_satisfies_ge (impl : RepoImpl) : Prop :=
  ∀ (lo v : Version),
    impl.semver.satisfies [⟨.ge, lo⟩] v = true ↔ impl.semver.versionLt v lo = false

/-- A `< hi` constraint is satisfied EXACTLY by the versions strictly below
    `hi`: `satisfies [⟨.lt, hi⟩] v` iff `v < hi`. Pins the `.lt` clause to the
    frozen strict order via `versionLt`, the upper-bound guarantee a caller needs
    from a `< hi` constraint. -/
def spec_satisfies_lt (impl : RepoImpl) : Prop :=
  ∀ (hi v : Version),
    impl.semver.satisfies [⟨.lt, hi⟩] v = true ↔ impl.semver.versionLt v hi = true

/-- A `≤ hi` constraint is satisfied EXACTLY by the versions that are not
    strictly above `hi`: `satisfies [⟨.le, hi⟩] v` iff `¬ (hi < v)`. Pins the
    `.le` clause to the frozen strict order via `versionLt` (mirror of the `.ge`
    lower-bound law). -/
def spec_satisfies_le (impl : RepoImpl) : Prop :=
  ∀ (hi v : Version),
    impl.semver.satisfies [⟨.le, hi⟩] v = true ↔ impl.semver.versionLt hi v = false

/-- A `> lo` constraint is satisfied EXACTLY by the versions strictly above
    `lo`: `satisfies [⟨.gt, lo⟩] v` iff `lo < v`. Pins the `.gt` clause to the
    frozen strict order via `versionLt` (the dual of the `.lt` upper-bound law). -/
def spec_satisfies_gt (impl : RepoImpl) : Prop :=
  ∀ (lo v : Version),
    impl.semver.satisfies [⟨.gt, lo⟩] v = true ↔ impl.semver.versionLt lo v = true

/-- An `== w` constraint is satisfied EXACTLY by the versions precedence-equal to
    `w`: `satisfies [⟨.eq, w⟩] v` iff `versionEq v w`. Pins the `.eq` clause to
    the frozen precedence-equality (which, by `spec_eq_characterisation`, ignores
    build metadata) rather than to structural equality. -/
def spec_satisfies_eq (impl : RepoImpl) : Prop :=
  ∀ (w v : Version),
    impl.semver.satisfies [⟨.eq, w⟩] v = true ↔ impl.semver.versionEq v w = true

/-- A conjunction of two clauses is satisfied iff BOTH are: a constraint range
    `[c1, c2]` admits exactly the versions admitted by each clause separately.
    Pins `satisfies` as the conjunction of its clauses. -/
def spec_satisfies_conj (impl : RepoImpl) : Prop :=
  ∀ (c1 c2 : Clause) (v : Version),
    impl.semver.satisfies [c1, c2] v = true ↔
      (impl.semver.satisfies [c1] v = true ∧ impl.semver.satisfies [c2] v = true)

-- ── select: witness + maximality (UNIQUE greatest matching) ────

/-- `select cs xs = some v` ⟹ the WITNESS: `v` is a member of `xs` and `v`
    satisfies `cs`. The selected version is a genuine matching candidate from
    the input list, not fabricated. -/
def spec_select_witness (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs : List Version) (v : Version),
    impl.semver.select cs xs = some v →
      v ∈ xs ∧ impl.semver.satisfies cs v = true

/-- `select cs xs = some v` ⟹ MAXIMALITY: no satisfying member of `xs` is
    strictly greater than `v` (`∀ w ∈ xs, satisfies cs w → ¬ lt v w`). Together
    with `spec_select_witness` this makes `select` return the greatest matching
    version. SemVer constraint resolution: the chosen "best match" is the
    newest version meeting the constraint. -/
def spec_select_maximal (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs : List Version) (v : Version),
    impl.semver.select cs xs = some v →
      ∀ (w : Version), w ∈ xs → impl.semver.satisfies cs w = true →
        impl.semver.versionLt v w = false

/-- `select cs xs = some v` ⟹ UNIQUENESS up to `eq`: any other matching member
    `w` that is itself maximal (no matching member strictly exceeds it) is
    `eq v`. The witness + maximality + this clause jointly characterise `select`
    as THE greatest matching version, unique up to precedence-equality. -/
def spec_select_unique (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs : List Version) (v : Version),
    impl.semver.select cs xs = some v →
      ∀ (w : Version), w ∈ xs → impl.semver.satisfies cs w = true →
        (∀ (u : Version), u ∈ xs → impl.semver.satisfies cs u = true →
          impl.semver.versionLt w u = false) →
        impl.semver.versionEq v w = true

/-- `select cs xs = none` ⟹ NO member of `xs` satisfies `cs`. Dual of the
    witness clause: an empty result means genuinely nothing matched, not that a
    match was missed. -/
def spec_select_none (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs : List Version),
    impl.semver.select cs xs = none →
      ∀ (v : Version), v ∈ xs → impl.semver.satisfies cs v = false

/-- `select` is a PERMUTATION INVARIANT (up to `eq`): reordering the candidate
    list cannot change whether a match is found nor which precedence-class of
    version is returned. For any permutation `xs ~ ys`: `select cs xs` succeeds
    exactly when `select cs ys` does, and whenever both succeed their results are
    `eq`. This is the order-independence a constraint resolver relies on — the
    "best match" is a property of the candidate *set*, not the traversal order. -/
def spec_select_perm (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs ys : List Version),
    xs.Perm ys →
      (impl.semver.select cs xs = none ↔ impl.semver.select cs ys = none) ∧
      (∀ (v w : Version),
        impl.semver.select cs xs = some v → impl.semver.select cs ys = some w →
          impl.semver.versionEq v w = true)

/-- `select` depends only on the SATISFYING sublist: dropping every candidate
    that fails the constraint leaves the result unchanged (`select cs xs` and
    `select cs (xs.filter (satisfies cs))` agree on success, and return `eq`
    results when both succeed). Non-matching versions are inert — a resolver may
    prune them without affecting the chosen best match. -/
def spec_select_filter (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs : List Version),
    (impl.semver.select cs xs = none ↔
       impl.semver.select cs (xs.filter (fun v => impl.semver.satisfies cs v)) = none) ∧
    (∀ (v w : Version),
      impl.semver.select cs xs = some v →
      impl.semver.select cs (xs.filter (fun v => impl.semver.satisfies cs v)) = some w →
        impl.semver.versionEq v w = true)

/-- Constraint evaluation depends only on the multiplicity of each clause:
    replacing the clause list with another list containing the same clauses the
    same number of times leaves satisfaction unchanged. -/
def spec_satisfies_clause_multiset (impl : RepoImpl) : Prop :=
  ∀ (cs ds : List Clause) (v : Version),
    (∀ (c : Clause), cs.count c = ds.count c) →
      impl.semver.satisfies cs v = impl.semver.satisfies ds v

/-- Selection depends only on the multiplicity of satisfying candidates: two
    candidate lists with the same satisfying versions either both select nothing,
    or select precedence-equal versions. -/
def spec_select_satisfying_multiset (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs ys : List Version),
    (∀ (v : Version),
      (xs.filter (fun w => impl.semver.satisfies cs w)).count v =
      (ys.filter (fun w => impl.semver.satisfies cs w)).count v) →
      (impl.semver.select cs xs = none ↔ impl.semver.select cs ys = none) ∧
      (∀ (v w : Version),
        impl.semver.select cs xs = some v →
        impl.semver.select cs ys = some w →
          impl.semver.versionEq v w = true)

/-- If all satisfying candidates appear in strictly increasing precedence order,
    selection returns the last satisfying candidate. -/
def spec_select_sorted_getLast (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs : List Version),
    List.Pairwise (fun a b => impl.semver.versionLt a b = true)
      (xs.filter (fun v => impl.semver.satisfies cs v)) →
      impl.semver.select cs xs =
        (xs.filter (fun v => impl.semver.satisfies cs v)).getLast?

/-- Changing build metadata on the constraints and candidates does not affect
    which precedence result is selected; a selected candidate is returned with
    its corresponding rewritten build metadata. -/
def spec_select_build_frame (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs : List Version)
      (f : Version → List String) (g : Clause → List String),
    match impl.semver.select cs xs with
    | none =>
        impl.semver.select
          (cs.map (fun c => { c with ver := { c.ver with build := g c } }))
          (xs.map (fun v => { v with build := f v })) = none
    | some v =>
        impl.semver.select
          (cs.map (fun c => { c with ver := { c.ver with build := g c } }))
          (xs.map (fun v => { v with build := f v })) =
            some { v with build := f v }

-- ── select: counting / structural characterisations ───────────

/-- `select cs xs` returns `none` EXACTLY when no candidate satisfies `cs`,
    stated as a length count: the result is `none` iff the satisfying sublist
    `xs.filter (satisfies cs ·)` is empty. Ties the empty-selection outcome to
    the count of matching candidates. -/
def spec_select_none_iff_satisfying_count_zero (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs : List Version),
    impl.semver.select cs xs = none ↔
      (xs.filter (fun v => impl.semver.satisfies cs v)).length = 0

/-- WEAKENING a constraint cannot lower the selected version: if every version
    satisfying `ds` also satisfies `cs` (so `cs` is the looser constraint), then
    the version selected under `ds` is not strictly greater than the one
    selected under `cs`. The looser constraint's best match is at least as high
    as the tighter one's. -/
def spec_select_constraint_weakening_monotone (impl : RepoImpl) : Prop :=
  ∀ (cs ds : List Clause) (xs : List Version) (v w : Version),
    (∀ (u : Version), impl.semver.satisfies ds u = true → impl.semver.satisfies cs u = true) →
      impl.semver.select ds xs = some v →
        impl.semver.select cs xs = some w →
          impl.semver.versionLt w v = false

/-- Restricting the candidate list to the precedence-equality class of the
    selected version leaves the selection unchanged: `select cs xs = some v`
    implies `select cs (xs.filter (versionEq v ·)) = some v`. The chosen
    representative is stable under pruning to its own `versionEq` class. -/
def spec_select_eq_class_filter_fixed (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs : List Version) (v : Version),
    impl.semver.select cs xs = some v →
      impl.semver.select cs (xs.filter (fun w => impl.semver.versionEq v w)) = some v

/-- Removing one structural copy of the selected version (when it occurs more
    than once) leaves a selection precedence-equal to the original: if
    `select cs xs = some v` and `xs.count v > 1`, then `select cs (xs.erase v)`
    is `some w` with `versionEq v w`. A duplicate winner survives one deletion
    up to precedence-equality. -/
def spec_select_erase_duplicate_preserves_eq (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs : List Version) (v : Version),
    impl.semver.select cs xs = some v →
      xs.count v > 1 →
        ∃ (w : Version),
          impl.semver.select cs (xs.erase v) = some w ∧
            impl.semver.versionEq v w = true

/-- In a duplicate-free candidate list, deleting the selected version yields an
    empty selection EXACTLY when it was the only satisfying candidate: with
    `xs.Nodup` and `select cs xs = some v`, `select cs (xs.erase v) = none` iff
    every other member of `xs` fails `cs`. -/
def spec_select_nodup_erase_selected_none_iff_unique_satisfying (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs : List Version) (v : Version),
    xs.Nodup →
      impl.semver.select cs xs = some v →
        (impl.semver.select cs (xs.erase v) = none ↔
          ∀ (w : Version), w ∈ xs → w ≠ v → impl.semver.satisfies cs w = false)

/-- Reordering the candidate list preserves the size of the winning
    precedence class: for `xs.Perm ys` with `select cs xs = some v` and
    `select cs ys = some w`, the count of satisfying candidates
    precedence-equal to the respective winner is the same on both sides.
    The multiplicity of the selected class is a permutation invariant. -/
def spec_select_perm_winning_eq_class_count (impl : RepoImpl) : Prop :=
  ∀ (cs : List Clause) (xs ys : List Version) (v w : Version),
    xs.Perm ys →
      impl.semver.select cs xs = some v →
        impl.semver.select cs ys = some w →
          (xs.filter (fun u => impl.semver.satisfies cs u && impl.semver.versionEq v u)).length =
            (ys.filter (fun u => impl.semver.satisfies cs u && impl.semver.versionEq w u)).length

-- ── order congruence + lexicographic characterisation ─────────

/-- Precedence-equal versions are interchangeable in every comparison against a
    third version: `versionEq a b` implies `compareV`, `versionLt`, and
    `versionEq` against any `c` agree in both argument positions. `versionEq` is
    a full congruence for the comparison family. -/
def spec_eq_order_congruence (impl : RepoImpl) : Prop :=
  ∀ (a b c : Version),
    impl.semver.versionEq a b = true →
      impl.semver.compareV a c = impl.semver.compareV b c ∧
      impl.semver.compareV c a = impl.semver.compareV c b ∧
      impl.semver.versionLt a c = impl.semver.versionLt b c ∧
      impl.semver.versionLt c a = impl.semver.versionLt c b ∧
      impl.semver.versionEq a c = impl.semver.versionEq b c ∧
      impl.semver.versionEq c a = impl.semver.versionEq c b

/-- `compareV a b = .lt` EXACTLY reproduces the lexicographic descent through
    the core axes, then the frozen pre-release field order: a strictly smaller
    `major`, or equal `major` with smaller `minor`, or equal `major.minor` with
    smaller `patch`, or an equal core with `preFieldCmpRef a.pre b.pre = .lt`.
    Anchored on the frozen `preFieldCmpRef`. -/
def spec_compare_lex_tuple_lt (impl : RepoImpl) : Prop :=
  ∀ (a b : Version),
    impl.semver.compareV a b = Ordering.lt ↔
      (a.major < b.major ∨
      (a.major = b.major ∧ a.minor < b.minor) ∨
      (a.major = b.major ∧ a.minor = b.minor ∧ a.patch < b.patch) ∨
      (a.major = b.major ∧ a.minor = b.minor ∧ a.patch = b.patch ∧
        preFieldCmpRef a.pre b.pre = Ordering.lt))

-- ── pre-release structural comparison laws (frozen-op anchored) ─

/-- A shared NON-EMPTY pre-release prefix is transparent to precedence: with
    equal core, `compareV ⟨…, pref ++ p, _⟩ ⟨…, pref ++ q, _⟩ = preCmpRef p q`
    for any `pref ≠ []`. Only the differing suffixes decide. Anchored on the
    frozen `preCmpRef`. -/
def spec_pre_common_prefix_cancels (impl : RepoImpl) : Prop :=
  ∀ (mj mn pa : Nat) (pref p q : List Ident) (b1 b2 : List String),
    pref ≠ [] →
      impl.semver.compareV ⟨mj, mn, pa, pref ++ p, b1⟩ ⟨mj, mn, pa, pref ++ q, b2⟩
        = preCmpRef p q

/-- The first differing identifier after a shared prefix decides precedence:
    with equal core, if `identCmpRef x y ≠ .eq` then
    `compareV ⟨…, pref ++ (x :: xs), _⟩ ⟨…, pref ++ (y :: ys), _⟩ = identCmpRef x y`
    regardless of the tails. Anchored on `identCmpRef`. -/
def spec_pre_first_difference_controls (impl : RepoImpl) : Prop :=
  ∀ (mj mn pa : Nat) (pref xs ys : List Ident) (x y : Ident) (b1 b2 : List String),
    identCmpRef x y ≠ Ordering.eq →
      impl.semver.compareV ⟨mj, mn, pa, pref ++ (x :: xs), b1⟩ ⟨mj, mn, pa, pref ++ (y :: ys), b2⟩
        = identCmpRef x y

/-- An equal identifier after a shared prefix reduces precedence to the tails:
    with equal core, if `identCmpRef x y = .eq` then
    `compareV ⟨…, pref ++ (x :: xs), _⟩ ⟨…, pref ++ (y :: ys), _⟩ = preCmpRef xs ys`.
    Anchored on the frozen `identCmpRef` / `preCmpRef`. -/
def spec_pre_equal_identifier_reduces_to_tail (impl : RepoImpl) : Prop :=
  ∀ (mj mn pa : Nat) (pref xs ys : List Ident) (x y : Ident) (b1 b2 : List String),
    identCmpRef x y = Ordering.eq →
      impl.semver.compareV ⟨mj, mn, pa, pref ++ (x :: xs), b1⟩ ⟨mj, mn, pa, pref ++ (y :: ys), b2⟩
        = preCmpRef xs ys

/-- Two equal-length pre-release prefixes that already differ fix precedence
    regardless of a shared appended suffix: with `p.length = q.length` and
    `preCmpRef p q ≠ .eq`, `compareV ⟨…, p ++ suffix, _⟩ ⟨…, q ++ suffix, _⟩
    = preCmpRef p q`. Anchored on `preCmpRef`. -/
def spec_pre_equal_length_suffix_preserves (impl : RepoImpl) : Prop :=
  ∀ (mj mn pa : Nat) (p q suffix : List Ident) (b1 b2 : List String),
    p.length = q.length → preCmpRef p q ≠ Ordering.eq →
      impl.semver.compareV ⟨mj, mn, pa, p ++ suffix, b1⟩ ⟨mj, mn, pa, q ++ suffix, b2⟩
        = preCmpRef p q

/-- With an equal core, precedence-equality is EXACTLY structural pre-release
    list equality: `versionEq ⟨…, p, _⟩ ⟨…, q, _⟩ = true` iff `p = q` (build
    metadata still irrelevant). -/
def spec_pre_eq_same_core_iff_pre_list_eq (impl : RepoImpl) : Prop :=
  ∀ (mj mn pa : Nat) (p q : List Ident) (b1 b2 : List String),
    impl.semver.versionEq ⟨mj, mn, pa, p, b1⟩ ⟨mj, mn, pa, q, b2⟩ = true ↔ p = q

/-- Adding the same offsets to the `major.minor.patch` axes of two versions
    leaves all three comparison projections unchanged: for any deltas
    `compareV`, `versionLt`, and `versionEq` of the shifted pair equal those of
    the original pair. Core precedence is translation-invariant. -/
def spec_core_translation_preserves_order (impl : RepoImpl) : Prop :=
  ∀ (a b : Version) (dMajor dMinor dPatch : Nat),
    let shift : Version → Version := fun v =>
      { v with major := v.major + dMajor, minor := v.minor + dMinor, patch := v.patch + dPatch }
    impl.semver.compareV (shift a) (shift b) = impl.semver.compareV a b ∧
    impl.semver.versionLt (shift a) (shift b) = impl.semver.versionLt a b ∧
    impl.semver.versionEq (shift a) (shift b) = impl.semver.versionEq a b

-- ── order towers over precedence-equality classes ─────────────

/-- Strict precedence is well-defined on precedence-equality classes: from
    `versionEq a b`, `versionLt b c`, and `versionEq c d` it follows that
    `versionLt a d` and `compareV a d = .lt`. A strict step is preserved when
    each endpoint is replaced by a precedence-equal version. -/
def spec_eq_lt_eq_composition (impl : RepoImpl) : Prop :=
  ∀ (a b c d : Version),
    impl.semver.versionEq a b = true →
    impl.semver.versionLt b c = true →
    impl.semver.versionEq c d = true →
      impl.semver.versionLt a d = true ∧ impl.semver.compareV a d = Ordering.lt

/-- A non-strict, then strict, then non-strict step compose to a strict
    increase: from `compareV a b ≠ .gt`, `versionLt b c`, and
    `compareV c d ≠ .gt` it follows that `versionLt a d` and
    `compareV a d = .lt`. The `≤`/`<`/`≤` tower collapses to `<`. -/
def spec_le_lt_le_tower (impl : RepoImpl) : Prop :=
  ∀ (a b c d : Version),
    impl.semver.compareV a b ≠ Ordering.gt →
    impl.semver.versionLt b c = true →
    impl.semver.compareV c d ≠ Ordering.gt →
      impl.semver.versionLt a d = true ∧ impl.semver.compareV a d = Ordering.lt

end Semver.Spec
