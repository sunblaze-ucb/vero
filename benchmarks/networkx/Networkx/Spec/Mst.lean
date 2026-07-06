import Networkx.Harness
import Networkx.Spec.Components

/-!
# Networkx.Spec.Mst

Specifications for the minimum-spanning-tree operations. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; an API is always reached
through `impl.networkx.<fn>`, never by calling the reference
`Networkx.<fn>` directly.

The headline obligations on `mstWeight` use the **witness ∧ minimality**
pattern of a unique optimum, anchored on a frozen ground-truth notion of a
*spanning forest*:

* a *spanning forest* of `g` is an edge subset `S` that uses only `g`'s
  edges, induces the same connected components as `g` over `g`'s nodes, and
  is acyclic (the forest edge-count identity `|S| + (#components of S) =
  (#nodes of g)`), validated by the frozen `spanningForest`;
* its *total weight* is the sum of the edge weights (the frozen
  `forestWeight`).

`mstWeight` must return a weight that **is realized by an actual spanning
forest** (witness) and that is **no larger than any spanning forest's
weight** (minimality) — so it is pinned to the genuine minimum-spanning-tree
weight; neither half alone is satisfiable by a degenerate implementation.

The frozen forest machinery below never refers to `impl`, so a degenerate
implementation cannot redefine what counts as a spanning forest.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── Frozen ground-truth forest machinery (DO NOT MODIFY) ──────────

/-- Every subset (the powerset) of a list, built structurally. The
    specification's own enumeration of candidate edge subsets, independent
    of any implementation. -/
def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => let r := subsets xs; r ++ r.map (x :: ·)

/-- The frozen total weight of an edge subset `S`: the sum of its edge
    weights. The specification's own ground truth. -/
def forestWeight (s : Graph) : Nat :=
  s.foldr (fun e acc => e.2.2 + acc) 0

/-- One frozen fixed-point round (mirrors the impl, but defined here so the
    spec owns its ground truth) over the frozen undirected adjacency. -/
def frozenReachRound (g : Graph) (reached : List Nat) : List Nat :=
  (frozenNodesOf g).foldl (fun acc v =>
    if acc.contains v then acc
    else if acc.any (fun u => uEdge g u v) then v :: acc else acc) reached

/-- Iterate the frozen round `n` times. -/
def frozenIterReach (g : Graph) : Nat → List Nat → List Nat
  | 0, r => r
  | n + 1, r => frozenIterReach g n (frozenReachRound g r)

/-- The frozen set of nodes reachable from `a` along undirected edges. -/
def frozenReachSet (g : Graph) (a : Nat) : List Nat :=
  frozenIterReach g ((frozenNodesOf g).length + 1) [a]

/-- The frozen undirected-connectivity test. -/
def frozenSameComp (g : Graph) (a b : Nat) : Bool :=
  (frozenReachSet g a).contains b

/-- The frozen number of connected components induced by edge set `s`,
    measured over `s`'s own endpoints, using the frozen undirected
    connectivity. -/
def frozenCompCount (s : Graph) : Nat :=
  let ns := frozenNodesOf s
  (ns.map (fun a => (frozenReachSet s a).mergeSort (· ≤ ·))).eraseDups.length

/-- `spanningForest g S`: `S` is a spanning forest of `g` — it is a
    sub-multiset of `g`'s edges (a sublist), induces the same connected
    components as `g` over `g`'s nodes (every pair of `g`'s nodes is
    connected in `S` exactly when it is in `g`), and is acyclic (the forest
    edge-count identity). The specification's frozen ground truth for
    "spanning forest". -/
def spanningForest (g s : Graph) : Bool :=
  s.isSublist g
    && (frozenNodesOf g).all (fun a => (frozenNodesOf g).all (fun b =>
          frozenSameComp g a b == frozenSameComp s a b))
    && (s.length + frozenCompCount s == (frozenNodesOf g).length)

-- ── mstWeight: witness ∧ minimality of a unique optimum ──────

/-- Minimality: the returned weight is no larger than the total weight of
    *any* spanning forest of `g`, so `mstWeight` cannot over-report: whatever
    spanning forest you exhibit, the optimum is `≤` its weight. An impl that
    reported a weight beaten by some spanning forest would violate this. -/
def spec_mst_minimal (impl : RepoImpl) : Prop :=
  ∀ (g s : Graph),
    spanningForest g s = true → impl.networkx.mstWeight g ≤ forestWeight s

/-- Witness: if `g` has *any* spanning forest, then the
    reported `mstWeight` is realized exactly by some spanning forest — there
    is a spanning forest `S` with `forestWeight S = mstWeight g`. So
    `mstWeight` cannot under-report: every reported optimum is certified by a
    concrete forest. Paired with minimality this pins the unique optimum. -/
def spec_mst_witness (impl : RepoImpl) : Prop :=
  ∀ (g s : Graph),
    spanningForest g s = true →
      ∃ t, spanningForest g t = true ∧ forestWeight t = impl.networkx.mstWeight g

/-- Exact optimum (witness ∧ minimality together): whenever a spanning
    forest exists, the reported weight is attained by some spanning forest
    `t` AND no spanning forest is cheaper than `t`. The unique-optimum
    statement — `mstWeight` equals the least achievable forest weight, pinned
    from both sides at once. -/
def spec_mst_optimal (impl : RepoImpl) : Prop :=
  ∀ (g s : Graph),
    spanningForest g s = true →
      ∃ t, spanningForest g t = true ∧
        forestWeight t = impl.networkx.mstWeight g ∧
        (∀ u, spanningForest g u = true → forestWeight t ≤ forestWeight u)

/-- The optimum is realized by a *structurally valid* forest (cross-API):
    whenever a spanning forest exists, the weight `mstWeight g` is
    attained by some spanning forest `t` that additionally satisfies the public
    forest edge-count identity `(#edges of t) + numConnectedComponents t =
    (#nodes of g)`. This ties the minimum-weight witness to the component
    bookkeeping of `numConnectedComponents`: the certificate for the optimum is
    not just *some* edge set of the right weight but an actual acyclic spanning
    forest whose edge count and component count balance against `g`'s node
    count. An impl that hit the right number but could only certify it with a
    forest whose edge/component bookkeeping disagreed with
    `numConnectedComponents` would violate this. -/
def spec_mst_witness_edges (impl : RepoImpl) : Prop :=
  ∀ (g s : Graph),
    spanningForest g s = true →
      ∃ t, spanningForest g t = true ∧
        forestWeight t = impl.networkx.mstWeight g ∧
        t.length + impl.networkx.numConnectedComponents t = (frozenNodesOf g).length

/-- The empty graph has zero MST weight (the empty spanning forest). A
    frozen anchor pinning the base case. -/
def spec_mst_empty (impl : RepoImpl) : Prop :=
  impl.networkx.mstWeight ([] : Graph) = 0

-- ── subsetWeight: matches the frozen weight, and composes ──────────

/-- `subsetWeight` agrees with the frozen forest weight `forestWeight`,
    pinning the edge-weight sum the rest of the spec relies on. -/
def spec_subset_weight_correct (impl : RepoImpl) : Prop :=
  ∀ (s : Graph),
    impl.networkx.subsetWeight s = forestWeight s

/-- `subsetWeight` is additive over concatenation: the weight of `s ++ t`
    is the sum of the two weights. Pins the weight function to be a genuine
    additive measure, not a cap or a max. -/
def spec_subset_weight_append (impl : RepoImpl) : Prop :=
  ∀ (s t : Graph),
    impl.networkx.subsetWeight (s ++ t)
      = impl.networkx.subsetWeight s + impl.networkx.subsetWeight t

/-- The empty subset has weight zero. -/
def spec_subset_weight_nil (impl : RepoImpl) : Prop :=
  impl.networkx.subsetWeight ([] : Graph) = 0

/-- Order-independence: `subsetWeight` is invariant under reordering the edge
    list — permuting the edges of `s` leaves the total weight unchanged. The
    weight of a forest is a property of its *multiset* of edges; this pins
    `subsetWeight` to a genuine commutative-monoid sum rather than any
    order-sensitive fold (a running max, a first/last-only reader, a
    difference). An impl whose total depended on edge order would violate
    this. -/
def spec_subset_weight_perm (impl : RepoImpl) : Prop :=
  ∀ (s t : Graph),
    s.Perm t → impl.networkx.subsetWeight s = impl.networkx.subsetWeight t

-- ── numTreeEdges: the forest edge-count identity ───────────────────

/-- The forest edge-count identity: `numTreeEdges g + numConnectedComponents
    g = (#nodes of g)`. A spanning forest of a graph on `n` nodes with `k`
    components has exactly `n − k` edges; this pins `numTreeEdges` to that
    count. An impl that miscounted tree edges (off by a component) would
    violate this. -/
def spec_num_tree_edges_identity (impl : RepoImpl) : Prop :=
  ∀ (g : Graph),
    impl.networkx.numTreeEdges g + impl.networkx.numConnectedComponents g
      = (frozenNodesOf g).length

/-- Any spanning forest is acyclic in the forest sense: a spanning forest
    `s` of `g` satisfies the forest edge-count identity over its own nodes —
    `(#edges of s) + (#components of s) = (#nodes of g)`. Ties the structural
    edge count of a spanning forest to the public component count through the
    frozen forest notion; an impl whose component count disagreed with the
    forest's own edge/node bookkeeping would violate this. -/
def spec_num_tree_edges_eq_forest (impl : RepoImpl) : Prop :=
  ∀ (g s : Graph),
    spanningForest g s = true →
      s.length + impl.networkx.numConnectedComponents s = (frozenNodesOf g).length

/-- Reachability round-trips through the component listing (cross-view): if `x`
    lies in the frozen reachable set of `a`, then `a` appears in `x`'s component
    listing and the two listings coincide — `componentOf g x = componentOf g a`.
    Anchored on the frozen `frozenReachSet` ground truth, this forces the public
    `componentOf` view to be reciprocal and canonical across every member of a
    class. -/
def spec_frozen_reachset_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a x : Nat),
    x ∈ frozenReachSet g a →
      a ∈ impl.networkx.componentOf g x ∧
        impl.networkx.componentOf g x = impl.networkx.componentOf g a

/-- `mstWeight g` is the least forest weight over the frozen enumeration of
    spanning forests: it equals the minimum of `forestWeight` across all
    subsets of `g`'s edges that pass the frozen `spanningForest g` test
    (`0` when there is none). Pins the reported optimum to the frozen
    ground-truth minimum on *every* graph. An impl that reported anything other
    than the least achievable spanning-forest weight would violate this. -/
def spec_mst_weight_eq_frozen_bruteforce (impl : RepoImpl) : Prop :=
  ∀ (g : Graph),
    impl.networkx.mstWeight g =
      ((((subsets g).filter (spanningForest g)).map forestWeight).min?).getD 0

/-- The MST weight depends only on the *multiset* of edges: reordering the edge
    list (`g.Perm h`) leaves `mstWeight g` equal to `mstWeight h`. The optimum
    is a property of the edge multiset, not the order edges are listed in. An
    impl whose reported weight drifted with edge order would violate this. -/
def spec_mst_weight_graph_perm (impl : RepoImpl) : Prop :=
  ∀ (g h : Graph),
    g.Perm h → impl.networkx.mstWeight g = impl.networkx.mstWeight h

/-- On a graph all of whose edges are self-loops (`e.1 = e.2.1` for every edge),
    `mstWeight g` is the least forest weight over the frozen spanning-forest
    enumeration measured by the edge-count balance `|s| + (#nodes of s) =
    (#nodes of g)`. Pins `mstWeight` on the loop-only region where no edge joins
    two distinct nodes — the optimum is still the frozen minimum over the valid
    edge subsets. An impl that mis-handled the loop-only case would violate
    this. -/
def spec_mst_self_loop_edge_count (impl : RepoImpl) : Prop :=
  ∀ (g : Graph),
    g.all (fun e => e.1 == e.2.1) = true →
      impl.networkx.mstWeight g =
        ((((subsets g).filter (fun s =>
          s.length + (frozenNodesOf s).length == (frozenNodesOf g).length)).map
            forestWeight).min?).getD 0

/-- `sameComponent` is exactly the frozen undirected-connectivity test:
    `sameComponent g a b = frozenSameComp g a b` for all `a`, `b`. Pins the
    public relation, as a `Bool`, to the frozen reachability ground truth on
    every pair — no over- or under-reporting, in either direction. An impl
    whose relation disagreed with the frozen connectivity on any pair (a merged
    component, a split one, or a one-directional reachability) would violate
    this. -/
def spec_same_component_eq_frozen_same_comp (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a b : Nat),
    impl.networkx.sameComponent g a b = frozenSameComp g a b

/-- The component listing is the stabilized reachable class: after
    `(#nodes of g)` frozen reachability rounds from `a`, one more round adds
    nothing (`frozenReachRound g r = r`), and `componentOf g a` is exactly that
    stabilized set, sorted (`r.mergeSort (· ≤ ·)`). Ties the public listing to
    the settled frozen reachability, presented in canonical order. An impl
    whose listing dropped a reachable node, kept an unreachable one, or drifted
    from the sorted stabilized class would violate this. -/
def spec_component_of_stabilized_class (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a : Nat),
    let r := frozenIterReach g (frozenNodesOf g).length [a]
    frozenReachRound g r = r ∧
      impl.networkx.componentOf g a = r.mergeSort (· ≤ ·)

/-- Reachability has settled at the reported class: the frozen reachable set of
    `a` is a fixed point of one more reachability round
    (`frozenReachRound g (frozenReachSet g a) = frozenReachSet g a`), so is
    `componentOf g a`, and the two agree member-for-member. Pins `componentOf`
    to a settled reachable class rather than a partial traversal. An impl whose
    listing was not closed under one more adjacency step, or whose membership
    diverged from the frozen reachable set, would violate this. -/
def spec_component_of_frozen_reachset_fixpoint (impl : RepoImpl) : Prop :=
  ∀ (g : Graph) (a : Nat),
    frozenReachRound g (frozenReachSet g a) = frozenReachSet g a ∧
      frozenReachRound g (impl.networkx.componentOf g a) = impl.networkx.componentOf g a ∧
      (∀ x, x ∈ impl.networkx.componentOf g a ↔ x ∈ frozenReachSet g a)
