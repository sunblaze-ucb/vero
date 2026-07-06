import Networkx.Harness

/-!
# Networkx.Spec.Components

Specifications for the connected-components operations. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; an API is always reached
through `impl.networkx.<fn>`, never by calling the reference
`Networkx.<fn>` directly.

The obligations pin `sameComponent` to be exactly the **undirected
connectivity relation**: an equivalence relation (reflexive, symmetric,
transitive) that contains every present edge and is closed under taking one
more adjacent step — i.e. the maximal mutually-reachable partition. The
ground truth is a frozen undirected-walk notion:

* an *undirected walk* `a → b` is a node list `[a, …, b]` whose every
  consecutive pair is connected by a present edge in *either* direction
  (validated by the frozen `isUWalk`);
* two nodes are in the same component exactly when some undirected walk
  joins them.

The frozen path machinery below (`uEdge`, `isUWalk`) is the
specification's own ground truth: it never refers to `impl`, so a
degenerate implementation cannot redefine what counts as connectivity.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── Frozen ground-truth connectivity machinery (DO NOT MODIFY) ──────────

/-- The frozen node set: the nodes that appear as an endpoint of some edge of
    `g`, de-duplicated. The specification's own ground truth for "the nodes of
    `g`" — the fixed domain over which components are counted — independent of
    any implementation. -/
def frozenNodesOf (g : Graph) : List Nat :=
  (g.foldr (fun e acc => e.1 :: e.2.1 :: acc) []).eraseDups

/-- The frozen **undirected** adjacency test: is there an edge between `a`
    and `b` in either direction? The specification's own ground truth,
    independent of any implementation. -/
def uEdge (g : Graph) (a b : Nat) : Bool :=
  g.any (fun e => (e.1 == a && e.2.1 == b) || (e.1 == b && e.2.1 == a))

/-- `isUWalk g a b nodes`: `nodes` is a valid undirected walk from `a` to
    `b` — it starts at `a`, ends at `b`, and every consecutive pair is a
    present edge in either direction. The empty list is not a walk; the
    singleton `[a]` is a walk iff `a = b`. -/
def isUWalk (g : Graph) (a b : Nat) : List Nat → Bool
  | [] => false
  | [x] => x == a && x == b
  | x :: y :: rest => x == a && uEdge g x y && isUWalk g y b (y :: rest)

-- ── sameComponent: the canonical undirected-connectivity equivalence ──────

/-- Reflexivity: every node is in its own component (the trivial walk
    `[a]`). The reflexive base case of the partition. -/
def spec_same_component_self (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a : Nat),
    impl.networkx.sameComponent g a a = true

/-- A present edge keeps its endpoints together: membership of *any*
    `(a, b, w)` in the graph forces `sameComponent g a b = true`. Mere
    presence of an undirected edge `a — b` is enough — no side condition on
    the weight. An impl that split a component across a present edge would
    violate this. -/
def spec_same_component_edge (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b w : Nat),
    (a, b, w) ∈ g →
      impl.networkx.sameComponent g a b = true

/-- Symmetry: `sameComponent` is symmetric —
    `sameComponent g a b = sameComponent g b a`. Connectivity does not
    depend on the order of the pair; an impl whose reachability was
    one-directional (treating the undirected graph as directed) would
    violate this. -/
def spec_same_component_symm (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b : Nat),
    impl.networkx.sameComponent g a b = impl.networkx.sameComponent g b a

/-- Transitivity: `sameComponent g a b` and `sameComponent g b c`
    imply `sameComponent g a c`. The composition law of the partition — if
    `a` and `b` share a component and `b` and `c` share a component, then
    `a` and `c` do. An impl whose relation was not transitive (declaring two
    overlapping pairs connected but denying the whole) would violate this. -/
def spec_same_component_trans (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b c : Nat),
    impl.networkx.sameComponent g a b = true →
    impl.networkx.sameComponent g b c = true →
      impl.networkx.sameComponent g a c = true

/-- Walk soundness: any undirected walk `a → b` of *any* length makes `a`
    and `b` share a component. `sameComponent` must absorb every node
    reachable by a chain of edges, however long the witnessing walk is. An
    impl that denied a component to two nodes joined by a multi-hop path
    would violate this. -/
def spec_same_component_of_walk (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b : Nat) (walk : List Nat),
    isUWalk g a b walk = true → impl.networkx.sameComponent g a b = true

/-- Walk completeness — no false positives: whenever
    `sameComponent g a b = true`, there *actually exists* an undirected walk
    `a → b` witnessing it. Together with `spec_same_component_of_walk` this
    makes `sameComponent` hold *exactly* when a walk exists, so it cannot
    over-report connectivity: a degenerate implementation that declared every
    pair connected (or merged separate components) would have to exhibit a
    walk through the frozen `isUWalk` ground truth, which does not exist, so
    it is forbidden. -/
def spec_same_component_complete (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b : Nat),
    impl.networkx.sameComponent g a b = true →
      ∃ walk, isUWalk g a b walk = true

/-- Component closure: a component is closed under one more adjacent step —
    if `a` and `x` share a component and there is an edge `x — y`, then `a`
    and `y` share a component. No component can be extended by an incident
    edge to a node outside it. -/
def spec_same_component_closed (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a x y w : Nat),
    impl.networkx.sameComponent g a x = true → (x, y, w) ∈ g →
      impl.networkx.sameComponent g a y = true

-- ── componentOf: the component is exactly the equivalence class ──────────

/-- `componentOf` membership characterizes the component: `x` is listed in
    `componentOf g a` exactly when `x` shares `a`'s component. Pins the
    returned node list to be precisely the equivalence class of `a`, neither
    omitting a reachable node nor inventing an unreachable one. -/
def spec_component_of_mem_iff (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a x : Nat),
    (x ∈ impl.networkx.componentOf g a) ↔ impl.networkx.sameComponent g a x = true

/-- `a` is always a member of its own component list. -/
def spec_component_of_self (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a : Nat),
    a ∈ impl.networkx.componentOf g a

/-- A node `b` shares `a`'s component exactly when `a` is listed in `b`'s
    component (symmetry routed through `componentOf`). Ties the two public
    views — the membership query and the component listing — together. -/
def spec_component_of_symm (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b : Nat),
    (b ∈ impl.networkx.componentOf g a) ↔ (a ∈ impl.networkx.componentOf g b)

/-- Canonical shape — no duplicates: `componentOf g a` is duplicate-free.
    Together with `spec_component_of_mem_iff` this forbids padding the component
    listing with repeats: the class is reported as a genuine set, each reachable
    node listed exactly once. An impl that emitted a reachable node twice would
    violate this. -/
def spec_component_of_nodup (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a : Nat),
    (impl.networkx.componentOf g a).Nodup

/-- Canonical shape — ascending order: `componentOf g a` is sorted
    non-decreasingly (every earlier entry is `≤` every later one). This pins
    the *presentation* order, not merely the contents. An impl that returned
    the reachable set in traversal order rather than sorted would violate
    this. -/
def spec_component_of_sorted (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a : Nat),
    List.Pairwise (· ≤ ·) (impl.networkx.componentOf g a)

/-- Canonical representative: members of one component get *identical*
    component listings — if `a` and `b` share a component then
    `componentOf g a = componentOf g b` as lists (not merely as sets). The
    component listing is a canonical form of the class, so it must not depend
    on which member you query it from. Combined with the Nodup/sorted shape
    specs it forces `componentOf g a` to be *the* sorted duplicate-free class
    list. An impl whose listing order or contents drifted between two members
    of the same component would violate this. -/
def spec_component_of_eq_of_same (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b : Nat),
    impl.networkx.sameComponent g a b = true →
      impl.networkx.componentOf g a = impl.networkx.componentOf g b

-- ── numConnectedComponents: counts and bounds ───────────────────────────

/-- The empty graph has zero components, and any non-empty graph has at
    least one: `numConnectedComponents g = 0` exactly when `g` has no edges.
    Pins the base case of the count. -/
def spec_num_components_zero_iff_empty (impl : RepoImpl) : Prop :=
  ∀ (g : Graph),
    impl.networkx.numConnectedComponents g = 0 ↔ g = []

/-- A present edge forces at least one component: any graph with an edge has
    `numConnectedComponents ≥ 1`. -/
def spec_num_components_pos_of_edge (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b w : Nat),
    (a, b, w) ∈ g →
      impl.networkx.numConnectedComponents g ≥ 1

/-- The count *is* the number of distinct classes (cross-API):
    `numConnectedComponents g` equals the number of distinct component
    listings `componentOf g a` taken over every node `a` of `g`
    (`frozenNodesOf g`, the de-duplicated endpoints). This forbids the degenerate
    `numConnectedComponents` that just reports a constant (e.g. always `1` for
    non-empty graphs, which passes both the zero-iff-empty and the `≥ 1`
    bounds): the count must agree, class for class, with the partition that
    `componentOf` induces. -/
def spec_num_components_eq_classes (impl : RepoImpl) : Prop :=
  ∀ (g : Graph),
    impl.networkx.numConnectedComponents g
      = ((frozenNodesOf g).map (fun a => impl.networkx.componentOf g a)).eraseDups.length

/-- The component listings account for every node exactly once: summing the
    lengths of the *distinct* component listings `componentOf g a` — one per
    node `a` of `g` (`frozenNodesOf g`), after collapsing repeats — recovers the
    total node count `(frozenNodesOf g).length`. The reported components neither
    double-count nor drop a node: they tile the node set. An impl whose listings
    overlapped, left a node uncovered, or padded a class would violate this. -/
def spec_component_partition_size_sum (impl : RepoImpl) : Prop :=
  ∀ (g : Graph),
    ((((frozenNodesOf g).map (fun a => impl.networkx.componentOf g a)).eraseDups).map
        (fun c => c.length)).sum
      = (frozenNodesOf g).length

/-- The component listing opens with the queried node exactly when that node is
    the least in its component: `componentOf g a` has `a` as its first entry iff
    `a ≤ x` for every `x` sharing `a`'s component. Ties the head of the reported
    listing to the minimum of the class it denotes. An impl that placed a
    non-minimal node first (or omitted `a` from the front when it is least)
    would violate this. -/
def spec_component_head_eq_self_iff_min (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a : Nat),
    (impl.networkx.componentOf g a).head? = some a ↔
      ∀ x, impl.networkx.sameComponent g a x = true → a ≤ x

/-- The component listing depends only on the *multiset* of edges, not their
    order: reordering the edge list (`g.Perm h`) leaves `componentOf g a`
    identical to `componentOf h a`. Pins the listing to a canonical form of the
    reachable class, independent of edge-traversal order. An impl whose listing
    drifted with edge order would violate this. -/
def spec_component_of_graph_perm (impl : RepoImpl) : Prop :=
  ∀ (g h : Graph) (a : Nat),
    g.Perm h →
      impl.networkx.componentOf g a = impl.networkx.componentOf h a

/-- Adding a redundant edge is a no-op on the whole component picture: if `a`
    and `b` are both already nodes of `g` and already share a component, then
    prepending the edge `(a, b, w)` leaves *every* component listing unchanged
    (`componentOf ((a,b,w)::g) x = componentOf g x` for all `x`) and leaves the
    component count unchanged. The reported state is invariant under an edge that
    adds no connectivity — an impl that shifted a listing or miscounted after a
    redundant edge would violate this. -/
def spec_internal_edge_component_frame (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b w : Nat),
    a ∈ frozenNodesOf g →
    b ∈ frozenNodesOf g →
    impl.networkx.sameComponent g a b = true →
      ((∀ x,
          impl.networkx.componentOf ((a, b, w) :: g) x
            = impl.networkx.componentOf g x) ∧
        impl.networkx.numConnectedComponents ((a, b, w) :: g)
          = impl.networkx.numConnectedComponents g)

/-- The component count depends only on the *multiset* of edges: reordering the
    edge list (`g.Perm h`) leaves `numConnectedComponents g` equal to
    `numConnectedComponents h`. The count is a property of the edge multiset,
    not the traversal order. An impl whose count drifted with edge order would
    violate this. -/
def spec_num_components_graph_perm (impl : RepoImpl) : Prop :=
  ∀ (g h : Graph),
    g.Perm h →
      impl.networkx.numConnectedComponents g = impl.networkx.numConnectedComponents h

/-- `sameComponent` depends only on the *multiset* of edges: reordering the
    edge list (`g.Perm h`) leaves `sameComponent g a b` equal to
    `sameComponent h a b` for every pair. Connectivity is a property of the
    edge multiset, not the order edges are listed in. An impl whose relation
    drifted with edge order would violate this. -/
def spec_same_component_graph_perm (impl : RepoImpl) : Prop :=
  ∀ (g h : Graph) (a b : Nat),
    g.Perm h →
      impl.networkx.sameComponent g a b = impl.networkx.sameComponent h a b
