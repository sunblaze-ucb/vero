import Dijkstar.Harness

/-!
# Dijkstar.Spec.ShortestPath

Specifications for the shortest-path operations. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`; an API is always reached through
`impl.dijkstar.<fn>`, never by calling the reference `Dijkstar.<fn>`
directly.

The headline obligations on `findPathCost` use the **witness ∧ minimality**
pattern of a unique optimum, anchored on a frozen ground-truth notion of a
walk:

* a *walk* `s → t` is a node list `[s, …, t]` whose every consecutive pair
  is a present edge (validated by the frozen `isWalk`);
* its *cost* is the sum of the consecutive edge weights (the frozen
  `walkCost`).

`findPathCost` must return a cost that **is realized by an actual walk**
(witness) and that is **no larger than any walk's cost** (minimality) — so
it is pinned to the genuine shortest-path cost; neither half alone is
satisfiable by a degenerate implementation.

The frozen path machinery below (`walkEdge`, `isWalk`, `walkCost`) is the
specification's own ground truth: it never refers to `impl`, so a degenerate
implementation cannot redefine what counts as a walk. It uses the same
first-match edge-weight rule as a directed edge.

DO NOT MODIFY — frozen.
-/

-- ── Frozen ground-truth path machinery (DO NOT MODIFY) ──────────

/-- The frozen weight of a direct edge `a → b`: the first matching
    `(from, to)` entry's weight, or `none`. This is the specification's
    own ground truth, independent of any implementation. -/
def walkEdge (g : Graph) (a b : Nat) : Option Nat :=
  (g.find? (fun e => e.1 == a && e.2.1 == b)).map (fun e => e.2.2)

/-- `isWalk g s t nodes`: `nodes` is a valid walk from `s` to `t` — it
    starts at `s`, ends at `t`, and every consecutive pair is a present
    edge. The empty list is not a walk; the singleton `[s]` is a walk iff
    `s = t`. -/
def isWalk (g : Graph) (s t : Nat) : List Nat → Bool
  | [] => false
  | [x] => x == s && x == t
  | x :: y :: rest => x == s && (walkEdge g x y).isSome && isWalk g y t (y :: rest)

/-- `walkCost g nodes`: the total weight of a walk — the sum of the
    consecutive edge weights along it. -/
def walkCost (g : Graph) : List Nat → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: rest => (walkEdge g x y).getD 0 + walkCost g (y :: rest)

-- ── Finite closure and table vocabulary ────────────────────────

/-- The finite node universe induced by a source and the graph endpoints. -/
def nodeUniverse (g : Graph) (s : Nat) : List Nat :=
  (s :: (g.map (fun e => e.1) ++ g.map (fun e => e.2.1))).eraseDups

/-- One forward endpoint-closure step over graph edges. -/
def reachStep (g : Graph) (seen : List Nat) : List Nat :=
  (seen ++ ((g.filter (fun e => seen.contains e.1)).map (fun e => e.2.1))).eraseDups

/-- Bounded forward endpoint closure. -/
def reachIter (g : Graph) : Nat → List Nat → List Nat
  | 0, seen => seen.eraseDups
  | n + 1, seen => reachStep g (reachIter g n seen)

/-- One predecessor-closure step over graph edges. -/
def reverseReachStep (g : Graph) (seen : List Nat) : List Nat :=
  (seen ++ ((g.filter (fun e => seen.contains e.2.1)).map (fun e => e.1))).eraseDups

/-- Bounded predecessor closure. -/
def reverseReachIter (g : Graph) : Nat → List Nat → List Nat
  | 0, seen => seen.eraseDups
  | n + 1, seen => reverseReachStep g (reverseReachIter g n seen)

/-- Lookup in a finite `(node, cost)` table. -/
def tableDistOf (d : Dist) (v : Nat) : Option Nat :=
  (d.find? (fun p => p.1 == v)).map Prod.snd

/-- Insert a cost row only when it improves the current table value. -/
def tableSetMin (d : Dist) (v c : Nat) : Dist :=
  match tableDistOf d v with
  | none => (v, c) :: d
  | some old => if c < old then (v, c) :: d else d

/-- Apply a single edge relaxation to a finite source-cost table. -/
def tableRelaxEdge (g : Graph) (d : Dist) (e : Nat × Nat × Nat) : Dist :=
  match tableDistOf d e.1, walkEdge g e.1 e.2.1 with
  | some df, some w => tableSetMin d e.2.1 (df + w)
  | _, _ => d

/-- Apply one graph-wide relaxation pass to a finite source-cost table. -/
def tableRelaxAll (g : Graph) (d : Dist) : Dist :=
  g.foldl (tableRelaxEdge g) d

/-- Cost-row order: increasing cost, then increasing node id. -/
def costRowLe (p q : Nat × Nat) : Bool :=
  decide (p.2 < q.2 ∨ (p.2 = q.2 ∧ p.1 ≤ q.1))

-- ── findPathCost: witness ∧ minimality of a unique optimum ──────

/-- Self distance is zero: the cost from a node to itself is `some 0`
    (the trivial walk `[s]`). A frozen anchor pinning the base case. -/
def spec_cost_self_zero (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s : Nat),
    impl.dijkstar.findPathCost g s s = some 0

/-- Single-edge upper bound: a present direct edge `s → t` of weight `w`
    bounds the shortest cost — `findPathCost` succeeds and returns a cost no
    larger than `w`. Ties the cost to the edge weights: the optimum can never
    exceed the cost of just taking the direct edge. Rejects an impl whose
    reported cost ever exceeds an available single edge. -/
def spec_cost_le_edge (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t w : Nat),
    impl.dijkstar.edgeWeight g s t = some w →
      ∃ c, impl.dijkstar.findPathCost g s t = some c ∧ c ≤ w

-- ── edgeWeight: membership and first-match determinism ──────────

/-- A successful `edgeWeight` is backed by a real edge in the graph: if
    `edgeWeight g a b = some w` then `(a, b, w)` is actually present. Pins the
    weight reported to a genuine `(from, to, weight)` triple, ruling out an
    impl that fabricates weights for absent edges. -/
def spec_edge_weight_mem (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b w : Nat),
    impl.dijkstar.edgeWeight g a b = some w → (a, b, w) ∈ g

/-- First-match determinism (the duplicate-edge convention): `(a, b, w)` is the
    *first* matching entry whenever an arbitrary prefix `pre` carries no
    `(a, b)` edge — `edgeWeight (pre ++ (a, b, w) :: g) a b = w`, regardless of
    `pre`'s non-matching edges or any later `(a, b)` entries in `g`. This makes
    the directed-edge weight well-defined under duplicates: a graph may list the
    same `(a, b)` pair more than once, and the convention pins which weight wins.
    A wrong impl that scanned to the last match, or merged duplicate weights,
    would violate this. -/
def spec_edge_weight_first_match (impl : RepoImpl) : Prop :=
  ∀ (g pre : Graph) (a b w : Nat),
    pre.find? (fun e => e.1 == a && e.2.1 == b) = none →
      impl.dijkstar.edgeWeight (pre ++ (a, b, w) :: g) a b = some w

-- ── reachable: ties to findPathCost, and is implied by an edge ──

/-- `none`/unreachable agreement: `findPathCost` fails to find a cost
    exactly when `reachable` reports the target is not reachable. Pins the
    two public APIs to be consistent. -/
def spec_none_iff_unreachable (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t : Nat),
    impl.dijkstar.findPathCost g s t = none ↔ impl.dijkstar.reachable g s t = false

/-- A present direct edge makes its target reachable: membership of *any*
    `(a, b, w)` in the graph forces `reachable g a b = true`. Mere presence of a
    direct `a → b` edge is enough — the precondition is membership alone, with no
    side condition on the edge's weight. An impl that denied reachability across a
    single present edge would violate this. -/
def spec_reachable_edge (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b w : Nat),
    (a, b, w) ∈ g →
      impl.dijkstar.reachable g a b = true

/-- Self-reachability: every node reaches itself (the trivial walk `[s]`).
    The reflexive base case of reachability. -/
def spec_reachable_self (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s : Nat),
    impl.dijkstar.reachable g s s = true

/-- The defining tie between the two query APIs: `reachable` reports `true`
    exactly when `findPathCost` finds a cost. Companion to
    `spec_none_iff_unreachable`, stated on the positive side. -/
def spec_reachable_iff_cost (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t : Nat),
    impl.dijkstar.reachable g s t = true ↔ impl.dijkstar.findPathCost g s t ≠ none

-- ── edgeWeight: matches the frozen first-match weight ───────────

/-- `edgeWeight` agrees with the frozen first-match edge weight `walkEdge`,
    pinning the directed-edge weight the rest of the spec relies on. -/
def spec_edge_weight_correct (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b : Nat),
    impl.dijkstar.edgeWeight g a b = walkEdge g a b

-- ════════════════════════════════════════════════════════════════
-- Unbounded shortest-path obligations.
--
-- These quantify over walks of *arbitrary* length: minimality and
-- completeness against every walk, the triangle inequality, and sub-path
-- optimality.
-- ════════════════════════════════════════════════════════════════

/-- Minimality: the returned cost is no larger than the cost of *any* walk
    from `s` to `t`, of *any* length — the shortest-path lower bound, so
    `findPathCost` cannot over-report. The optimum must dominate every
    alternative route, including ones with far more hops than the cheapest. An
    impl that reported a cost beaten by some longer-but-cheaper walk would
    violate this. -/
def spec_cost_minimal_unbounded (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t c : Nat),
    impl.dijkstar.findPathCost g s t = some c →
      ∀ (walk : List Nat), isWalk g s t walk = true → c ≤ walkCost g walk

/-- Completeness: if *any* walk `s → t` exists — of *any* length —
    `findPathCost` must return `some`. No reachable target may be
    reported `none`, however long the only witnessing walk is; this closes the
    under-reporting hole where an impl returns `some` only for the source
    itself or a direct edge and `none` for everything multi-hop. -/
def spec_cost_complete_unbounded (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t : Nat) (walk : List Nat),
    isWalk g s t walk = true → impl.dijkstar.findPathCost g s t ≠ none

/-- Unbounded path-existence bound: a returned cost is realized by a walk
    *and* is below any walk's cost, so for every walk `s → t` the optimum is
    a `some c` with `c ≤` that walk's cost. The achievability-and-domination
    statement over arbitrary-length walks; the unbounded companion of
    `spec_cost_le_edge`. -/
def spec_cost_le_walk (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t : Nat) (walk : List Nat),
    isWalk g s t walk = true →
      ∃ c, impl.dijkstar.findPathCost g s t = some c ∧ c ≤ walkCost g walk

/-- Triangle inequality: the optimum to `t` never exceeds the optimum to an
    intermediate `u` plus a direct edge `u → t`. When
    `findPathCost g s u = some cu` and `edgeWeight g u t = some w`,
    `findPathCost g s t = some c` with `c ≤ cu + w`. Extending a best route to
    `u` by one more edge to `t` can never beat the best route straight to `t`;
    an impl that ignored a relaxing predecessor edge would over-report `t`'s
    cost and violate this. -/
def spec_cost_triangle (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s u t cu w : Nat),
    impl.dijkstar.findPathCost g s u = some cu →
    impl.dijkstar.edgeWeight g u t = some w →
      ∃ c, impl.dijkstar.findPathCost g s t = some c ∧ c ≤ cu + w

/-- Sub-path optimality: for any walk `s → t` that passes through an
    intermediate node `v` (so the walk is `pre ++ v :: post`), *both* legs are
    individually optimal against their own segment of the walk — the optimum to
    `v` is at most the prefix's cost `walkCost (pre ++ [v])`, AND the optimum
    from `v` to `t` is at most the suffix's cost `walkCost (v :: post)`. Every
    interior node of a route bounds the optimum to and from it by the route's
    own two segments; an impl claiming a cheaper end-to-end route than its own
    pieces admit would violate this. -/
def spec_subpath_optimal (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t v : Nat) (pre post : List Nat),
    isWalk g s t (pre ++ v :: post) = true →
      (∃ c, impl.dijkstar.findPathCost g s v = some c ∧ c ≤ walkCost g (pre ++ [v]))
    ∧ (∃ d, impl.dijkstar.findPathCost g v t = some d ∧ d ≤ walkCost g (v :: post))

-- ── reachable: transitivity and walk laws ───────────────────────

/-- Reachability transitivity: `reachable g s u` and `reachable g u t` imply
    `reachable g s t`. The composition law of reachability — if you can get from
    `s` to `u` and from `u` to `t`, then `t` is reachable from `s`. An impl whose
    reachability relation was not transitive (declaring two legs reachable but
    denying the whole) would violate this. -/
def spec_reachable_trans (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s u t : Nat),
    impl.dijkstar.reachable g s u = true → impl.dijkstar.reachable g u t = true →
      impl.dijkstar.reachable g s t = true

/-- Walk reachability: any walk `s → t` of *any* length makes `t` reachable
    from `s`. Closes the hole where `reachable` denies a target reached only by
    a multi-hop path, however long the only witnessing walk is. -/
def spec_reachable_of_walk_unbounded (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t : Nat) (walk : List Nat),
    isWalk g s t walk = true → impl.dijkstar.reachable g s t = true

-- ── edgeWeight: absence characterization ────────────────────────

/-- Absence characterization: `edgeWeight g a b = none` exactly when no edge
    `(a, b, _)` is present in the graph. The bidirectional companion to
    `spec_edge_weight_mem`, pinning the failure case: `edgeWeight` reports
    `none` if and only if there genuinely is no direct edge `a → b`. -/
def spec_edge_weight_none_iff_absent (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b : Nat),
    impl.dijkstar.edgeWeight g a b = none ↔ ∀ w, (a, b, w) ∉ g

-- ════════════════════════════════════════════════════════════════
-- Global all-pairs consistency obligations.
--
-- The specs below state consequences of shortest-path optimality as relations
-- among `findPathCost` values at different node pairs — global consistency
-- facts about the whole cost table.
-- ════════════════════════════════════════════════════════════════

/-- Cost subadditivity (all-pairs consistency): the optimum from `s` to `t`
    never exceeds the optimum from `s` to an intermediate `u` plus the optimum
    from `u` to `t`. Whenever both `findPathCost g s u = some a` and
    `findPathCost g u t = some b` are finite, `findPathCost g s t = some c`
    with `c ≤ a + b`. The triangle inequality of the shortest-path metric,
    composing two *arbitrary* optima (not a single edge as in
    `spec_cost_triangle`): it pins the cost table to be globally consistent
    across all three node pairs at once. -/
def spec_cost_subadditive (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s u t a b : Nat),
    impl.dijkstar.findPathCost g s u = some a →
    impl.dijkstar.findPathCost g u t = some b →
      ∃ c, impl.dijkstar.findPathCost g s t = some c ∧ c ≤ a + b

/-- Tight last edge (optimality is exact, not merely an upper bound): if the
    optimum from `s` to `t` is finite and *positive*, then it is realized
    exactly by relaxing some predecessor — there is a node `u` with a direct
    edge `u → t` of weight `w` such that `findPathCost g s u = some cu` and
    `c = cu + w`. The converse direction of the relaxation bound: not only is
    the optimum `≤ cu + w` for every predecessor (the upper bound), some
    predecessor attains it with *equality*, so the cost is pinned to the exact
    least value and cannot be over-reported by any margin. -/
def spec_cost_predecessor_tight (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t c : Nat),
    impl.dijkstar.findPathCost g s t = some c → c > 0 →
      ∃ u w cu, impl.dijkstar.edgeWeight g u t = some w ∧
        impl.dijkstar.findPathCost g s u = some cu ∧ c = cu + w

/-- Optimal-substructure split (Bellman optimality, both legs): for any walk
    `s → t` that threads an intermediate node `v` (so the walk is
    `pre ++ v :: post`), all three optima are finite and the whole-trip optimum
    is dominated by the sum of the two leg optima — `findPathCost g s v = some a`,
    `findPathCost g v t = some b`, `findPathCost g s t = some c`, and `c ≤ a + b`.
    Strengthens `spec_subpath_optimal` (which bounds only the `s → v` prefix
    leg) to compose *both* legs into a bound on the end-to-end optimum. -/
def spec_cost_optimal_split (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t v : Nat) (pre post : List Nat),
    isWalk g s t (pre ++ v :: post) = true →
      ∃ a b c,
        impl.dijkstar.findPathCost g s v = some a ∧
        impl.dijkstar.findPathCost g v t = some b ∧
        impl.dijkstar.findPathCost g s t = some c ∧ c ≤ a + b

/-- Achievability by a bounded walk (witness): whenever
    `findPathCost g s t = some c`, that exact cost is realized by an actual
    walk `s → t` whose length stays within `g.length + 1`. So `findPathCost`
    cannot under-report the true cost: every returned optimum is certified by a
    concrete walk, and that walk is no longer than the graph's edge count plus
    one. An impl that returned a cost no real walk attains, or one realizable
    only by an over-long walk, would violate this. -/
def spec_cost_exact_simple_witness (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t c : Nat),
    impl.dijkstar.findPathCost g s t = some c →
      ∃ walk, isWalk g s t walk = true ∧ walkCost g walk = c
        ∧ walk.length ≤ g.length + 1

-- ════════════════════════════════════════════════════════════════
-- Cross-graph monotonicity and front-decomposition obligations.
--
-- The specs above all work within a single fixed graph `g`. The obligations
-- below cover two more:
--
--   * Edge-set growth (`append`): appending edges to the END of the graph can
--     only help — neither the optimum nor reachability can worsen. (Stated on
--     `append`, not `prepend`: prepending can rewrite a present pair's
--     first-match weight upward and so is *not* monotone.)
--
--   * The walk's FIRST edge: the source-side mirror of the last-edge laws,
--     rooting the remaining optimum at the first hop out of `s`.
-- ════════════════════════════════════════════════════════════════

/-- Append monotonicity of cost (edge growth never hurts): appending edges to
    the end of the graph cannot increase any optimum. When `findPathCost g s t`
    is finite, `findPathCost (g ++ extra) s t` is finite and no larger.

    Stated on `append` (not `prepend`): prepending is *not* monotone, since a
    prepended edge can shadow an existing one and rewrite its weight upward. An
    impl that let extra edges raise an existing optimum, or drop it to `none`,
    would violate this. -/
def spec_cost_append_monotone (impl : RepoImpl) : Prop :=
  ∀ (g extra : Graph) (s t c : Nat),
    impl.dijkstar.findPathCost g s t = some c →
      ∃ c', impl.dijkstar.findPathCost (g ++ extra) s t = some c' ∧ c' ≤ c

/-- Append monotonicity of reachability (edge growth never disconnects): if `t`
    is reachable from `s` in `g`, it stays reachable in `g ++ extra`. The
    reachability companion of `spec_cost_append_monotone`: adding edges to the
    end of the graph can only add routes, never remove them, so no target that
    was reachable can become unreachable. An impl that lost a connection when
    edges were appended would violate this. -/
def spec_reachable_append_monotone (impl : RepoImpl) : Prop :=
  ∀ (g extra : Graph) (s t : Nat),
    impl.dijkstar.reachable g s t = true →
      impl.dijkstar.reachable (g ++ extra) s t = true

/-- First-edge relaxation bound (front triangle): the optimum from `s` to `t`
    never exceeds a direct edge `s → x` of weight `w` followed by the optimum
    from `x` to `t`. When `edgeWeight g s x = some w` and
    `findPathCost g x t = some cx`, `findPathCost g s t = some c` with
    `c ≤ w + cx`. The source-side mirror of `spec_cost_triangle` (which relaxes
    the LAST edge `u → t`): here the relaxing edge is the FIRST hop out of `s`.
    Taking one step `s → x` and then the best route onward can never beat the
    best route straight to `t`; an impl that ignored a relaxing outgoing edge
    from the source would violate this. -/
def spec_cost_first_edge (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s x t w cx : Nat),
    impl.dijkstar.edgeWeight g s x = some w →
    impl.dijkstar.findPathCost g x t = some cx →
      ∃ c, impl.dijkstar.findPathCost g s t = some c ∧ c ≤ w + cx

/-- Tight first edge (front optimality is exact): if the optimum from `s` to
    `t` is finite and *positive*, then it is realised exactly by some first hop —
    there is a node `x` with a direct edge `s → x` of weight `w` such that
    `findPathCost g x t = some cx` and `c = w + cx`. The source-side mirror of
    `spec_cost_predecessor_tight` (which pins the LAST edge): not merely an upper
    bound, the optimum's leading edge attains the cost with *equality*, so the
    reported value is pinned to the exact least cost from the front and cannot be
    over-reported by any margin. -/
def spec_cost_first_hop_tight (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t c : Nat),
    impl.dijkstar.findPathCost g s t = some c → c > 0 →
      ∃ x w cx, impl.dijkstar.edgeWeight g s x = some w ∧
        impl.dijkstar.findPathCost g x t = some cx ∧ c = w + cx

/-- Every interior node of a walk is reachable from the source: for any walk
    `s → t` that threads a node `v` (so the walk is `pre ++ v :: post`), `v` is
    reachable from `s`. Closes the hole where `reachable` could deny a node that
    demonstrably lies on a path out of `s`. -/
def spec_prefix_node_reachable (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t v : Nat) (pre post : List Nat),
    isWalk g s t (pre ++ v :: post) = true →
      impl.dijkstar.reachable g s v = true

-- ════════════════════════════════════════════════════════════════
-- Finite closure, table, and canonical-form obligations.
-- ════════════════════════════════════════════════════════════════

/-- Reachability census: over the finite node universe determined by the source
    and graph endpoints, the number of nodes reported reachable agrees with the
    endpoint closure obtained from the graph. -/
def spec_reachable_census_closure (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s : Nat),
    (nodeUniverse g s).countP (fun v => impl.dijkstar.reachable g s v)
      = (reachIter g (g.length + 1) [s]).length

/-- Addressed-prefix consistency: a node occurring on a valid walk is the node
    at its recorded index, and the prefix ending there is itself a valid walk
    from the original source. -/
def spec_walk_first_occurrence_prefix (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t v : Nat) (walk : List Nat),
    isWalk g s t walk = true → v ∈ walk →
      walk.getD (walk.idxOf v) s = v ∧
      isWalk g s v (walk.take (walk.idxOf v) ++ [v]) = true ∧
      impl.dijkstar.reachable g s v = true

/-- Cost-table closure: the finite source-cost table is unchanged by applying
    one graph-wide relaxation pass using the graph's edge weights. -/
def spec_cost_table_closed (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s : Nat),
    let d : Dist := (nodeUniverse g s).filterMap (fun v =>
      (impl.dijkstar.findPathCost g s v).map (fun c => (v, c)))
    tableRelaxAll g d = d

/-- Backward coverage: whenever a target is reachable from a source, the source
    is included in the bounded predecessor closure rooted at that target. -/
def spec_reachable_reverse_closure (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t : Nat),
    impl.dijkstar.reachable g s t = true →
      s ∈ reverseReachIter g (g.length + 1) [t]

/-- Sorted row uniqueness: the sorted finite source-cost rows are the unique
    duplicate-free list with the same rows in the same cost-row order. -/
def spec_cost_rows_sorted_unique (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s : Nat) (xs : List (Nat × Nat)),
    let rows : List (Nat × Nat) := (nodeUniverse g s).filterMap (fun v =>
      (impl.dijkstar.findPathCost g s v).map (fun c => (v, c)))
    let canon : List (Nat × Nat) := rows.mergeSort costRowLe
    xs.Nodup →
    List.Pairwise (fun p q => costRowLe p q = true) xs →
    (∀ p, p ∈ xs ↔ p ∈ canon) →
      xs = canon

/-- Exact append frame: if every visible edge in the enlarged graph is already
    covered by the old source-cost table, appending those edges preserves all
    source-cost queries. -/
def spec_append_nonimproving_exact (impl : RepoImpl) : Prop :=
  ∀ (g extra : Graph) (s : Nat),
    (∀ (a b w c : Nat),
      walkEdge (g ++ extra) a b = some w →
      impl.dijkstar.findPathCost g s a = some c →
        ∃ cb, impl.dijkstar.findPathCost g s b = some cb ∧ cb ≤ c + w) →
      ∀ t, impl.dijkstar.findPathCost (g ++ extra) s t = impl.dijkstar.findPathCost g s t

-- ════════════════════════════════════════════════════════════════
-- Reachable-set closure, table stability, and edge-perturbation
-- consistency obligations.
-- ════════════════════════════════════════════════════════════════

/-- Forward edge closure of reachability: if `t` is reachable from `s` and there
    is a direct edge `a → b`, then reaching `a` from `s` forces `b` reachable
    from `s`. Stated on `a`: whenever `s` reaches `a` and `a → b` is a present
    edge, `s` reaches `b`. Reachable sets are closed under following one more
    outgoing edge; an impl that stopped one hop short of a reachable frontier
    node would violate this. -/
def spec_reachable_forward_edge_closed (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s a b w : Nat),
    impl.dijkstar.reachable g s a = true →
    impl.dijkstar.edgeWeight g a b = some w →
      impl.dijkstar.reachable g s b = true

/-- Backward edge closure of reachability: a direct edge `a → b` prefixed onto
    any route from `b` to `t` keeps `t` reachable — if `edgeWeight g a b = some w`
    and `reachable g b t`, then `reachable g a t`. The predecessor-side companion
    of `spec_reachable_forward_edge_closed`: adding one leading edge cannot
    disconnect a reachable target. -/
def spec_reachable_backward_edge_closed (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b t w : Nat),
    impl.dijkstar.edgeWeight g a b = some w →
    impl.dijkstar.reachable g b t = true →
      impl.dijkstar.reachable g a t = true

/-- Reachability equals the finite forward closure: `reachable g s t` holds
    exactly when `t` lies in the bounded forward endpoint closure rooted at `s`.
    Pins the semantic reachability query to the frozen graph-closure iteration,
    node for node — every reachable target is enumerated by the closure and
    nothing else is. -/
def spec_reachable_forward_closure_exact (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t : Nat),
    impl.dijkstar.reachable g s t = true ↔ t ∈ reachIter g (g.length + 1) [s]

/-- Relaxation fixpoint of the cost table: the finite source-cost table built
    from `findPathCost` is stable under a *second* graph-wide relaxation pass —
    at every node its lookup after two passes equals its lookup after one.
    Companion to `spec_cost_table_closed`, pinning stability to persist under
    repeated relaxation rather than only the first pass. -/
def spec_cost_table_two_pass_idempotent_at_node (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t : Nat),
    let d : Dist := (nodeUniverse g s).filterMap (fun v =>
      (impl.dijkstar.findPathCost g s v).map (fun c => (v, c)))
    tableDistOf (tableRelaxAll g (tableRelaxAll g d)) t
      = tableDistOf (tableRelaxAll g d) t

/-- Zero self-loop is cost-neutral: appending a zero-weight self-loop `(v, v, 0)`
    to the end of the graph changes no source-cost query — `findPathCost` at
    every `(s, t)` is identical before and after. A self-loop of no weight adds
    no route worth taking; an impl that let such an edge perturb any optimum
    would violate this. -/
def spec_append_zero_self_loop_cost_neutral (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t v : Nat),
    impl.dijkstar.findPathCost (g ++ [(v, v, 0)]) s t
      = impl.dijkstar.findPathCost g s t

/-- Cost equals the predecessor-relaxation minimum: for a non-source target the
    optimum is exactly the least `cu + w` over every present edge `u → t` whose
    source `u` has a finite optimum, and the source's own cost is `some 0`. The
    exactness form of the last-edge bound — not merely dominated by some
    predecessor relaxation but equal to their finite minimum. -/
def spec_cost_predecessor_min_exact (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t : Nat),
    let candidates : List Nat := g.filterMap (fun e =>
      if e.2.1 == t then
        match impl.dijkstar.findPathCost g s e.1, impl.dijkstar.edgeWeight g e.1 t with
        | some cu, some w => some (cu + w)
        | _, _ => none
      else none)
    let best : Option Nat := candidates.foldl (fun acc c =>
      match acc with
      | none => some c
      | some old => some (Nat.min old c)) none
    impl.dijkstar.findPathCost g s t = if s == t then some 0 else best

/-- Dominated appended edge is irrelevant: appending an edge `a → b` of weight
    `w` whose target `b` is already reached from `s` at cost no worse than
    `ca + w` (where `ca` is the optimum to `a`) leaves every source-cost query
    unchanged. An edge that offers no improvement over an existing route can be
    added without shifting any optimum. -/
def spec_append_dominated_edge_irrelevant (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t a b w ca cb : Nat),
    impl.dijkstar.findPathCost g s a = some ca →
    impl.dijkstar.findPathCost g s b = some cb →
    cb ≤ ca + w →
      impl.dijkstar.findPathCost (g ++ [(a, b, w)]) s t
        = impl.dijkstar.findPathCost g s t

/-- Fresh zero-edge source inherits costs: introducing a brand-new source `s'`
    (absent from the graph's node universe) with a single zero edge `s' → s`
    gives `s'` exactly the costs `s` already had to every old target `t ≠ s'` —
    `findPathCost (g ++ [(s', s, 0)]) s' t = findPathCost g s t`. Prepending a
    zero hop to a fresh source shifts the whole cost profile unchanged. -/
def spec_zero_edge_new_source_shift (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s s' t : Nat),
    s' ∉ nodeUniverse g s → t ≠ s' →
      impl.dijkstar.findPathCost (g ++ [(s', s, 0)]) s' t
        = impl.dijkstar.findPathCost g s t

/-- Concatenated-walk cost bound: a walk `s → u` followed by a walk `u → t`
    bounds the optimum to `t` — for any valid `left` (walk `s → u`) and `right`
    (walk `u → t`), `findPathCost g s t = some c` with
    `c ≤ walkCost g left + walkCost g right`. Gluing two routes at a shared node
    is a route, so its combined cost dominates the optimum; the two-leg
    achievability companion of the single-walk bound. -/
def spec_cost_le_concatenated_walk (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s u t : Nat) (left right : List Nat),
    isWalk g s u left = true →
    isWalk g u t right = true →
      ∃ c, impl.dijkstar.findPathCost g s t = some c ∧
        c ≤ walkCost g left + walkCost g right

/-- Every edge weight on an optimal witness is bounded by the optimum: if
    `findPathCost g s t = some c` and a walk `pre ++ a :: b :: post` realizes
    that cost exactly (`walkCost = c`), then any edge `a → b` on it has weight
    `w ≤ c`. No single hop of a cheapest route can cost more than the whole
    route; an impl reporting an optimum smaller than one of its own edges would
    violate this. -/
def spec_optimal_walk_edge_weight_le_cost (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (s t a b c w : Nat) (pre post : List Nat),
    impl.dijkstar.findPathCost g s t = some c →
    isWalk g s t (pre ++ a :: b :: post) = true →
    walkCost g (pre ++ a :: b :: post) = c →
    impl.dijkstar.edgeWeight g a b = some w →
      w ≤ c

/-- Weight inflation never lowers the optimum: raising every listed edge weight
    by any pointwise-nondecreasing `inflate` keeps reachability and can only
    raise costs — the inflated-graph optimum is `some` exactly when the original
    is, and is no smaller. Weights only ever push costs up; an impl that let a
    uniformly heavier graph report a cheaper or newly-`none` route would violate
    this. -/
def spec_weight_inflate_monotone (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (inflate : Nat → Nat → Nat → Nat) (s t : Nat),
    (∀ (a b w : Nat), w ≤ inflate a b w) →
      match
        impl.dijkstar.findPathCost
          (g.map (fun e => (e.1, e.2.1, inflate e.1 e.2.1 e.2.2))) s t,
        impl.dijkstar.findPathCost g s t
      with
      | some hi, some lo => lo ≤ hi
      | none, none => True
      | _, _ => False
