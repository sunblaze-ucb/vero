import Textdistance.Impl.Edit
import Textdistance.Bundle
import Textdistance.Harness
import Textdistance.Spec.Edit
import Textdistance.Test

/-!
# Textdistance

Root import hub for the edit-distance benchmark.

Two operations over sequences of symbol codes (`List Nat`):
`levenshtein a b` is the minimum number of single-symbol insertions,
deletions, and substitutions transforming `a` into `b`; `lcs a b` is the
length of the longest common subsequence of `a` and `b`. Distances and
lengths are `Nat`. Behaviour is pinned by `Spec/Edit.lean`.
-/
