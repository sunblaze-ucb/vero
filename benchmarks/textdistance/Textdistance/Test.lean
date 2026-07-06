import Textdistance.Impl.Edit

/-!
# Textdistance.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations inside the `code` markers in
`Impl/Edit.lean`.

DO NOT MODIFY — infrastructure.
-/

open Textdistance

-- ── levenshtein ────────────────────────────────────────────────
#guard levenshtein [] [] == 0
#guard levenshtein [1, 2, 3] [1, 2, 3] == 0           -- identical: distance 0
#guard levenshtein [] [1, 2, 3] == 3                  -- three insertions
#guard levenshtein [1, 2, 3] [] == 3                  -- three deletions
#guard levenshtein [1, 2, 3] [1, 9, 3] == 1           -- one substitution
#guard levenshtein [1, 2, 3] [1, 3] == 1              -- one deletion
#guard levenshtein [1, 3] [1, 2, 3] == 1              -- one insertion
#guard levenshtein [1, 2, 3, 4] [2, 4, 5] == 3        -- classic mixed edits

-- ── lcs ────────────────────────────────────────────────────────
#guard lcs [] [] == 0
#guard lcs [1, 2, 3] [] == 0                          -- empty has no common subsequence
#guard lcs [1, 2, 3] [1, 2, 3] == 3                   -- identical: full length
#guard lcs [1, 2, 3] [1, 9, 3] == 2                   -- common subsequence [1,3]
#guard lcs [1, 2, 3, 4, 1] [3, 4, 1, 2, 1] == 3       -- e.g. [3,4,1] or [2,4,1]
#guard lcs [1, 2, 3] [4, 5, 6] == 0                   -- disjoint
