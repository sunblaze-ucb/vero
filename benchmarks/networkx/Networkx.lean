import Networkx.Impl.Components
import Networkx.Impl.Mst
import Networkx.Bundle
import Networkx.Harness
import Networkx.Spec.Components
import Networkx.Spec.Mst
import Networkx.Test

/-!
# Networkx

Root import hub for the pure-graph-algorithms benchmark over an undirected
weighted graph `Graph := List (Nat × Nat × Nat)` (an edge `(u, v, w)`
connects `u` and `v` in either direction; weights are `Nat`).

* **Components** — `numConnectedComponents` / `sameComponent` /
  `componentOf`: the partition of the nodes into maximal mutually-reachable
  sets, and its associated queries.

* **Mst** — `mstWeight` / `numTreeEdges` / `subsetWeight`: the least total
  weight of a spanning forest, plus the forest edge-count and edge-weight-sum
  operations.

The benchmark models undirected connectivity and minimum-spanning-forest
WEIGHT only — `mstWeight` is a single `Nat`, with no returned tree edge
sequence. Behaviour is pinned by `Spec/Components.lean` and `Spec/Mst.lean`.
-/
