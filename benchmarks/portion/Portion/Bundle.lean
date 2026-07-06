import Portion.Impl.Algebra

/-!
# Portion.Bundle

Per-package implementation bundle for the `Portion` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure PortionBundle where
  contains     : Portion.ContainsSig
  complement   : Portion.ComplementSig
  union        : Portion.UnionSig
  intersection : Portion.IntersectionSig
  difference   : Portion.DifferenceSig
  isEmpty      : Portion.IsEmptySig
