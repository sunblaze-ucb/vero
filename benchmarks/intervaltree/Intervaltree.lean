import Intervaltree.Impl.Merge
import Intervaltree.Bundle
import Intervaltree.Harness
import Intervaltree.Spec.Merge
import Intervaltree.Test

/-!
# Intervaltree

Root import hub for the interval-set-algebra benchmark over half-open
`[lo, hi)` intervals of `Int`. The three API functions are `overlaps`
(do two intervals share a point), `mergeOverlaps` (canonicalise a set of
intervals), and `chop` (remove a range from every interval).

`mergeOverlaps ivs` returns the unique minimal set of disjoint intervals
covering the same point set as `ivs`, sorted by `lo` with strict gaps
between consecutive intervals (touching intervals like `[0,2),[2,4)`
coalesce into `[0,4)`). Behaviour is pinned by `Spec/Merge.lean`,
anchored on the frozen `covered` point-membership predicate.
-/
