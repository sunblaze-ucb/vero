-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Dijkstar.Impl.ShortestPath

Single-source shortest-path operations. The headline operation is
`findPathCost g s t`: the minimum total weight of a path from `s` to `t`,
or `none` if `t` is unreachable. Companion observers are `edgeWeight`
(direct-edge weight) and `reachable`.

A graph is an association list of weighted directed edges
`(from, to, weight)` with `Nat` nodes and nonnegative `Nat` weights; the
first matching `(from, to)` entry fixes a directed edge's weight.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A weighted directed graph: an association list of edges
    `(from, to, weight)`. Nodes are `Nat`; weights are nonnegative `Nat`.
    The first matching `(from, to)` entry fixes that edge's weight. -/
abbrev Graph := List (Nat × Nat × Nat)

/-- A working distance table: an association list mapping a node to its
    current best known distance. A node absent from the table is treated
    as unreachable (distance `+∞`). The first matching entry wins. -/
abbrev Dist := List (Nat × Nat)

namespace Dijkstar

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `findPathCost g s t`: the minimum total weight of a walk from `s` to
    `t`, or `none` if `t` is unreachable from `s`. -/
abbrev FindPathCostSig := Graph → Nat → Nat → Option Nat

/-- `edgeWeight g a b`: the weight of the direct edge `a → b` (the first
    matching entry), or `none` if there is no such edge. -/
abbrev EdgeWeightSig := Graph → Nat → Nat → Option Nat

/-- `reachable g s t`: whether `t` is reachable from `s`. -/
abbrev ReachableSig := Graph → Nat → Nat → Bool

end Dijkstar

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=edgeWeight
-- !benchmark @end code_aux def=edgeWeight

def Dijkstar.edgeWeight : Dijkstar.EdgeWeightSig :=
-- !benchmark @start code def=edgeWeight
  fun g a b => (g.find? (fun e => e.1 == a && e.2.1 == b)).map (fun e => e.2.2)
-- !benchmark @end code def=edgeWeight

-- !benchmark @start code_aux def=findPathCost
-- Private helpers of the reference implementation.

def distOf (d : Dist) (v : Nat) : Option Nat :=
  (d.find? (fun p => p.1 == v)).map Prod.snd

def setMin (d : Dist) (v c : Nat) : Dist :=
  match distOf d v with
  | none => (v, c) :: d
  | some old => if c < old then (v, c) :: d else d

def relaxEdge (g : Graph) (d : Dist) (e : Nat × Nat × Nat) : Dist :=
  match distOf d e.1, Dijkstar.edgeWeight g e.1 e.2.1 with
  | some df, some w => setMin d e.2.1 (df + w)
  | _, _ => d

def relaxList (g : Graph) (L : Graph) (d : Dist) : Dist :=
  L.foldl (relaxEdge g) d

def relaxAll (g : Graph) (d : Dist) : Dist :=
  relaxList g g d

def iterRelax (g : Graph) : Nat → Dist → Dist
  | 0, d => d
  | n + 1, d => iterRelax g n (relaxAll g d)
-- !benchmark @end code_aux def=findPathCost

def Dijkstar.findPathCost : Dijkstar.FindPathCostSig :=
-- !benchmark @start code def=findPathCost
  fun g s t => distOf (iterRelax g (g.length + 1) [(s, 0)]) t
-- !benchmark @end code def=findPathCost

-- !benchmark @start code_aux def=reachable
-- !benchmark @end code_aux def=reachable

def Dijkstar.reachable : Dijkstar.ReachableSig :=
-- !benchmark @start code def=reachable
  fun g s t => (Dijkstar.findPathCost g s t).isSome
-- !benchmark @end code def=reachable
