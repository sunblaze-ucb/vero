import Difflib.Impl.SequenceMatcher
import Difflib.Bundle
import Difflib.Harness
import Difflib.Spec.SequenceMatcher
import Difflib.Test

/-!
# Difflib

Root import hub for the sequence-matching benchmark. Sequences are
`List Nat`; elements are compared for equality only.

API surface (`impl.difflib.<fn>`):
* `findLongestMatch a b` — the single longest contiguous block
  `(i, j, k)` with `a[i:i+k] = b[j:j+k]`, chosen canonically
  (k maximal → i minimal → j minimal); `(0, 0, 0)` when nothing matches.
* `getMatchingBlocks a b` — a list of maximal matching blocks describing
  the matching subsequences, ending in the sentinel `(|a|, |b|, 0)`.
* `matchSize a b` — the length of the longest matching block.

Behaviour is pinned by `Spec/SequenceMatcher.lean`, against a frozen
ground-truth notion of a common contiguous block (`isCommonBlock`). Only
the per-call longest-match property and the structural invariants of the
block list are specified; no spec claims global optimality of the block
decomposition.
-/
