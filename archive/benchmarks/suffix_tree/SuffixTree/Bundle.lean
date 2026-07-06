import SuffixTree.Impl.SuffixTreeNode
import SuffixTree.Impl.SuffixTree

/-!
# SuffixTree.Bundle

Per-package implementation bundle for the `SuffixTree` root package.
Collects all 4 API signatures into one structure.

In `Harness.lean`, `RepoImpl` wraps this bundle in a single field
(`suffixTree : SuffixTreeBundle`).

Note: the structure's auto-constructor is renamed to `toBundleData`
to avoid a name collision with the `mk` field (which stores the
`SuffixTree.MkSig` API function).

DO NOT MODIFY — benchmark infrastructure.
-/

structure SuffixTreeBundle where
  toBundleData ::
  mk              : SuffixTree.MkSig
  buildSuffixTree : SuffixTree.BuildSuffixTreeSig
  addSuffix       : SuffixTree.AddSuffixSig
  search          : SuffixTree.SearchSig
