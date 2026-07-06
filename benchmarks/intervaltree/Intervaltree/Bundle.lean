import Intervaltree.Impl.Merge

/-!
# Intervaltree.Bundle

Per-package implementation bundle for the `Intervaltree` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure IntervaltreeBundle where
  overlaps       : Intervaltree.OverlapsSig
  mergeOverlaps  : Intervaltree.MergeOverlapsSig
  chop           : Intervaltree.ChopSig
