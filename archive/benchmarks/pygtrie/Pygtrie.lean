import Pygtrie.Impl.Trie
import Pygtrie.Bundle
import Pygtrie.Harness
import Pygtrie.Spec.Trie
import Pygtrie.Test

/-!
# Pygtrie

Root import hub for the longest-prefix-match benchmark.

The benchmark targets the longest-prefix-match operation: given a
query key, return the longest stored key that is a prefix of it. The
headline obligation set is witness ∧ maximality ∧ completeness on
`longestPrefix`, anchored on the frozen `List.isPrefixOf`.

## Deliberate scope

Keys are sequences of `Nat`; values are plain `Nat`. The prefix APIs
(`prefixes`, `longestPrefix`) return KEYS, not `(key, value)` items.
`get k t` is `Option Nat` (`none` on a miss). Behaviour is pinned by
`Spec/Trie.lean`.
-/
