import Difflib.Impl.SequenceMatcher

/-!
# Difflib.Bundle

Per-package implementation bundle for the `Difflib` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure DifflibBundle where
  findLongestMatch  : Difflib.FindLongestMatchSig
  getMatchingBlocks : Difflib.GetMatchingBlocksSig
  matchSize         : Difflib.MatchSizeSig
