import Dijkstar.Impl.ShortestPath

/-!
# Dijkstar.Bundle

Per-package implementation bundle for the `Dijkstar` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure DijkstarBundle where
  findPathCost : Dijkstar.FindPathCostSig
  edgeWeight   : Dijkstar.EdgeWeightSig
  reachable    : Dijkstar.ReachableSig
