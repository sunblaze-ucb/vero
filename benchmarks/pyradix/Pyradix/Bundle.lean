import Pyradix.Impl.Radix

/-!
# Pyradix.Bundle

Per-package implementation bundle for the `Pyradix` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure PyradixBundle where
  searchBest  : Pyradix.SearchBestSig
  searchWorst : Pyradix.SearchWorstSig
  searchExact : Pyradix.SearchExactSig
  add         : Pyradix.AddSig
  delete      : Pyradix.DeleteSig
  covered     : Pyradix.CoveredSig
