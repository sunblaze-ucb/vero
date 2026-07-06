import Dijkstar.Impl.ShortestPath
import Dijkstar.Bundle
import Dijkstar.Harness
import Dijkstar.Spec.ShortestPath
import Dijkstar.Test

/-!
# Dijkstar

Root import hub for the single-source shortest-path benchmark.

The API is shortest-path COST: `findPathCost g s t` returns the minimum
total weight of a path from `s` to `t`, or `none` if unreachable, over a
graph of weighted directed edges with nonnegative `Nat` weights. Companion
observers are `edgeWeight` (direct-edge weight) and `reachable`.

Behaviour is pinned by Spec/ShortestPath.lean against a frozen ground-truth
notion of a walk (`isWalk` / `walkCost`): the returned cost is realized by
an actual walk and is no larger than any walk's cost.

Scope: COST only — there is no returned node/edge sequence (no path
reconstruction).
-/
