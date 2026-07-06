-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Networkx.Impl.Components

Connected-components operations. The headline operations are
`numConnectedComponents` (the number of connected components) and
`sameComponent` (whether two nodes lie in the same component), plus
`componentOf` (the component's node list).

A graph is an association list of weighted **undirected** edges `(u, v, w)`
with `Nat` nodes and `Nat` weights; an edge `(u, v, w)` connects `u` and `v`
in *either* direction (weights are ignored by the connectivity queries). Two
nodes lie in the same component when one is reachable from the other along
undirected edges.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A weighted **undirected** graph: an association list of edges
    `(u, v, w)`. Nodes are `Nat`; weights are `Nat`. An edge `(u, v, w)`
    connects `u` and `v` in either direction (weights are ignored by the
    connectivity queries). -/
abbrev Graph := List (Nat × Nat × Nat)

namespace Networkx

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `numConnectedComponents g`: the number of connected components of `g`,
    i.e. the number of distinct maximal mutually-reachable node sets among
    the nodes that appear in `g`'s edges. -/
abbrev NumConnectedComponentsSig := Graph → Nat

/-- `sameComponent g a b`: whether `a` and `b` lie in the same connected
    component — i.e. `b` is reachable from `a` along undirected edges. -/
abbrev SameComponentSig := Graph → Nat → Nat → Bool

/-- `componentOf g a`: the sorted node list of the connected component
    containing `a` (the set of nodes reachable from `a`). -/
abbrev ComponentOfSig := Graph → Nat → List Nat

end Networkx

-- !benchmark @start global_aux
/-- The nodes that appear as an endpoint of some edge of `g`, de-duplicated. -/
def nodesOf (g : Graph) : List Nat :=
  (g.foldr (fun e acc => e.1 :: e.2.1 :: acc) []).eraseDups

/-- Undirected adjacency: is there an edge between `a` and `b` (in either
    direction)? Weights are ignored. -/
def adjacent (g : Graph) (a b : Nat) : Bool :=
  g.any (fun e => (e.1 == a && e.2.1 == b) || (e.1 == b && e.2.1 == a))
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=numConnectedComponents
def reachRound (g : Graph) (reached : List Nat) : List Nat :=
  (nodesOf g).foldl (fun acc v =>
    if acc.contains v then acc
    else if acc.any (fun u => adjacent g u v) then v :: acc else acc) reached

def iterReach (g : Graph) : Nat → List Nat → List Nat
  | 0, r => r
  | n + 1, r => iterReach g n (reachRound g r)

/-- The set of nodes reachable from `a` along undirected edges. -/
def reachSet (g : Graph) (a : Nat) : List Nat :=
  iterReach g ((nodesOf g).length + 1) [a]
-- !benchmark @end code_aux def=numConnectedComponents

def Networkx.numConnectedComponents : Networkx.NumConnectedComponentsSig :=
-- !benchmark @start code def=numConnectedComponents
  fun g =>
    let ns := nodesOf g
    (ns.map (fun a => (reachSet g a).mergeSort (· ≤ ·))).eraseDups.length
-- !benchmark @end code def=numConnectedComponents

-- !benchmark @start code_aux def=sameComponent
-- !benchmark @end code_aux def=sameComponent

def Networkx.sameComponent : Networkx.SameComponentSig :=
-- !benchmark @start code def=sameComponent
  fun g a b => (reachSet g a).contains b
-- !benchmark @end code def=sameComponent

-- !benchmark @start code_aux def=componentOf
-- !benchmark @end code_aux def=componentOf

def Networkx.componentOf : Networkx.ComponentOfSig :=
-- !benchmark @start code def=componentOf
  fun g a => (reachSet g a).mergeSort (· ≤ ·)
-- !benchmark @end code def=componentOf
