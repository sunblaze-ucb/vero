import Textdistance.Impl.Edit

/-!
# Textdistance.Bundle

Per-package implementation bundle for the `Textdistance` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure TextdistanceBundle where
  levenshtein : Textdistance.LevenshteinSig
  lcs         : Textdistance.LcsSig
