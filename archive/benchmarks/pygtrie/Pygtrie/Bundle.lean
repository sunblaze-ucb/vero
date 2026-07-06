import Pygtrie.Impl.Trie

/-!
# Pygtrie.Bundle

Per-package implementation bundle for the `Pygtrie` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure PygtrieBundle where
  set            : Pygtrie.SetSig
  get            : Pygtrie.GetSig
  hasKey         : Pygtrie.HasKeySig
  longestPrefix  : Pygtrie.LongestPrefixSig
  prefixes       : Pygtrie.PrefixesSig
