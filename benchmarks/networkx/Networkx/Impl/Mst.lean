import Networkx.Impl.Components

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Networkx.Impl.Mst

Minimum-spanning-forest operations over an undirected weighted graph. The
headline operation is `mstWeight`: the least total weight of a spanning
forest of `g`. Companions are `numTreeEdges` (the number of edges in a
spanning forest) and `subsetWeight` (the total weight of an edge subset).

A *spanning forest* of `g` is a subset `S` of `g`'s edges that is acyclic
and connects exactly the same node pairs as `g` does — every component of
`g` is spanned, none merged. Its weight is the sum of its edge weights;
`mstWeight` is the minimum such weight.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Networkx

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `mstWeight g`: the least total weight over all spanning forests of `g`
    (the total weight of a minimum spanning tree / forest). `0` for the
    empty graph. -/
abbrev MstWeightSig := Graph → Nat

/-- `numTreeEdges g`: the number of edges in any spanning forest of `g`,
    i.e. `(#nodes) − (#components)`. -/
abbrev NumTreeEdgesSig := Graph → Nat

/-- `subsetWeight S`: the total weight of an edge subset `S`. -/
abbrev SubsetWeightSig := Graph → Nat

end Networkx

-- !benchmark @start global_aux
/-- Every subset (the powerset) of a list. -/
def subsetsOf {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => let r := subsetsOf xs; r ++ r.map (x :: ·)

/-- The number of connected components of the graph spanned by edge set `s`,
    measured over `s`'s own endpoints. -/
def compCount (s : Graph) : Nat :=
  let ns := nodesOf s
  (ns.map (fun a => (reachSet s a).mergeSort (· ≤ ·))).eraseDups.length
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=subsetWeight
-- !benchmark @end code_aux def=subsetWeight

def Networkx.subsetWeight : Networkx.SubsetWeightSig :=
-- !benchmark @start code def=subsetWeight
  fun s => s.foldr (fun e acc => e.2.2 + acc) 0
-- !benchmark @end code def=subsetWeight

-- !benchmark @start code_aux def=numTreeEdges
-- !benchmark @end code_aux def=numTreeEdges

def Networkx.numTreeEdges : Networkx.NumTreeEdgesSig :=
-- !benchmark @start code def=numTreeEdges
  fun g => (nodesOf g).length - Networkx.numConnectedComponents g
-- !benchmark @end code def=numTreeEdges

-- !benchmark @start code_aux def=mstWeight
/-- Whether `s` is a spanning forest of `g`. -/
def isSpanningForest (g s : Graph) : Bool :=
  s.isSublist g
    && (nodesOf g).all (fun a => (nodesOf g).all (fun b =>
          Networkx.sameComponent g a b == Networkx.sameComponent s a b))
    && (s.length + compCount s == (nodesOf g).length)
-- !benchmark @end code_aux def=mstWeight

def Networkx.mstWeight : Networkx.MstWeightSig :=
-- !benchmark @start code def=mstWeight
  fun g =>
    let cands := (subsetsOf g).filter (isSpanningForest g)
    ((cands.map Networkx.subsetWeight).min?).getD 0
-- !benchmark @end code def=mstWeight
