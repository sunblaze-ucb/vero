import Networkx.Impl.Components
import Networkx.Impl.Mst

/-!
# Networkx.Bundle

Per-package implementation bundle for the `Networkx` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure NetworkxBundle where
  numConnectedComponents : Networkx.NumConnectedComponentsSig
  sameComponent          : Networkx.SameComponentSig
  componentOf            : Networkx.ComponentOfSig
  mstWeight              : Networkx.MstWeightSig
  numTreeEdges           : Networkx.NumTreeEdgesSig
  subsetWeight           : Networkx.SubsetWeightSig
