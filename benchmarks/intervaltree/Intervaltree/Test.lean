import Intervaltree.Impl.Merge

/-!
# Intervaltree.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations inside the `code` markers in
`Impl/Merge.lean`.

DO NOT MODIFY — infrastructure.
-/

open Intervaltree

-- ── overlaps ───────────────────────────────────────────────────
#guard overlaps { lo := 0, hi := 3 } { lo := 2, hi := 5 } == true    -- share [2,3)
#guard overlaps { lo := 0, hi := 2 } { lo := 2, hi := 4 } == false   -- touch only (half-open)
#guard overlaps { lo := 0, hi := 5 } { lo := 1, hi := 2 } == true    -- containment
#guard overlaps { lo := 0, hi := 1 } { lo := 5, hi := 6 } == false   -- disjoint
#guard overlaps { lo := 2, hi := 4 } { lo := 0, hi := 3 } == true    -- symmetric to first

-- ── mergeOverlaps ──────────────────────────────────────────────
-- touching intervals coalesce (strict gap requirement)
#guard mergeOverlaps [{ lo := 0, hi := 2 }, { lo := 2, hi := 4 }] == [{ lo := 0, hi := 4 }]
-- overlapping intervals coalesce, order-independent
#guard mergeOverlaps [{ lo := 2, hi := 5 }, { lo := 0, hi := 3 }] == [{ lo := 0, hi := 5 }]
-- disjoint intervals stay separate, sorted by lo
#guard mergeOverlaps [{ lo := 5, hi := 7 }, { lo := 0, hi := 2 }] == [{ lo := 0, hi := 2 }, { lo := 5, hi := 7 }]
-- empty intervals are dropped
#guard mergeOverlaps [{ lo := 3, hi := 3 }, { lo := 0, hi := 2 }] == [{ lo := 0, hi := 2 }]
#guard mergeOverlaps [] == []
-- nested intervals coalesce to the outer one
#guard mergeOverlaps [{ lo := 0, hi := 10 }, { lo := 3, hi := 5 }] == [{ lo := 0, hi := 10 }]

-- ── chop ───────────────────────────────────────────────────────
-- chop the middle out, splitting into two pieces
#guard chop 2 4 [{ lo := 0, hi := 6 }] == [{ lo := 0, hi := 2 }, { lo := 4, hi := 6 }]
-- chop covering the whole interval removes it
#guard chop 0 10 [{ lo := 2, hi := 5 }] == []
-- chop outside the interval leaves it untouched
#guard chop 10 20 [{ lo := 0, hi := 5 }] == [{ lo := 0, hi := 5 }]
-- chop trimming the left end
#guard chop 0 3 [{ lo := 1, hi := 5 }] == [{ lo := 3, hi := 5 }]
-- chop trimming the right end
#guard chop 3 9 [{ lo := 1, hi := 5 }] == [{ lo := 1, hi := 3 }]
