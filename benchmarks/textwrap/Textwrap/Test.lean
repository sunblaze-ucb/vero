import Textwrap.Impl.Wrap

/-!
# Textwrap.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations inside the `code` markers in
`Impl/Wrap.lean`.

DO NOT MODIFY — infrastructure.
-/

open Textwrap

-- ── lineWidth ──────────────────────────────────────────────────
#guard lineWidth [] == 0
#guard lineWidth [2, 3] == 5
#guard lineWidth [4, 4, 4] == 12

-- ── wrap: greedy first-fit ─────────────────────────────────────
-- width 5: 2+2=4 fits, +2=6 > 5 → new line.
#guard wrap [2, 2, 2] 5 == [[2, 2], [2]]
-- width 5: 3 fits alone, 3+3=6 > 5 → each on its own line.
#guard wrap [3, 3] 5 == [[3], [3]]
-- empty input → no lines.
#guard wrap [] 5 == []
-- over-long word (10 > 5) occupies its own over-wide line.
#guard wrap [10] 5 == [[10]]
-- a word that still fits is packed; 1+1=2 ≤ 2, 1+1=2 again → two lines.
#guard wrap [1, 1, 1, 1] 2 == [[1, 1], [1, 1]]
-- over-long word then a normal word: 10 alone, then 1.
#guard wrap [10, 1] 5 == [[10], [1]]
-- words preserved under flatten.
#guard (wrap [2, 2, 2] 5).flatten == [2, 2, 2]

-- ── shorten: maximal fitting prefix ────────────────────────────
-- 2+2=4 ≤ 5, +2=6 > 5 → keep first two.
#guard shorten [2, 2, 2] 5 == [2, 2]
-- 3 ≤ 5, 3+3=6 > 5 → keep first.
#guard shorten [3, 3] 5 == [3]
-- first word over-long → keep nothing.
#guard shorten [10] 5 == []
-- empty input → empty.
#guard shorten [] 5 == []
