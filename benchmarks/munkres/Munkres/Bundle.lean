import Munkres.Impl.Assign

/-!
# Munkres.Bundle

Per-package implementation bundle for the `Munkres` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure MunkresBundle where
  padMatrix      : Munkres.PadMatrixSig
  makeCostMatrix : Munkres.MakeCostMatrixSig
  compute        : Munkres.ComputeSig
  assignmentCost : Munkres.AssignmentCostSig
