import Difflib.Impl.SequenceMatcher

/-!
# Difflib.Test

Executable conformance tests. `#guard` assertions run against the
implementations inside the `code` markers in `Impl/SequenceMatcher.lean`.

DO NOT MODIFY — infrastructure.
-/

open Difflib

-- ── findLongestMatch ────────────────────────────────────────────
-- "abxcd" vs "abcd": longest common run is "ab" at (0,0,2).
#guard findLongestMatch [97, 98, 120, 99, 100] [97, 98, 99, 100] == (0, 0, 2)
-- "ab" vs "acab": longest run "ab" appears at b-index 2, not 0.
#guard findLongestMatch [97, 98] [97, 99, 97, 98] == (0, 2, 2)
-- tie on k=1: "ba" vs "ab" — both 'b'(0,1) and 'a'(1,0) are length-1 runs;
-- the canonical (i minimal) match is (0,1,1).
#guard findLongestMatch [98, 97] [97, 98] == (0, 1, 1)
-- self-match covers the whole sequence.
#guard findLongestMatch [1, 2, 3] [1, 2, 3] == (0, 0, 3)
-- disjoint sequences: no common element, sentinel (0,0,0).
#guard findLongestMatch [7, 8, 9] [1, 2, 3] == (0, 0, 0)
-- empty inputs.
#guard findLongestMatch ([] : Sequence) [1, 2] == (0, 0, 0)
#guard findLongestMatch [1, 2] ([] : Sequence) == (0, 0, 0)

-- ── getMatchingBlocks ───────────────────────────────────────────
-- "abxcd" vs "abcd": two blocks + sentinel.
#guard getMatchingBlocks [97, 98, 120, 99, 100] [97, 98, 99, 100]
        == [(0, 0, 2), (3, 2, 2), (5, 4, 0)]
-- "abcbc" vs "bc": the leftmost longest "bc" then sentinel.
#guard getMatchingBlocks [97, 98, 99, 98, 99] [98, 99] == [(1, 0, 2), (5, 2, 0)]
-- empty vs empty: just the sentinel.
#guard getMatchingBlocks ([] : Sequence) ([] : Sequence) == [(0, 0, 0)]
-- singleton match.
#guard getMatchingBlocks [5] [5] == [(0, 0, 1), (1, 1, 0)]
-- no common element: only the sentinel.
#guard getMatchingBlocks [7, 8] [1, 2] == [(2, 2, 0)]

-- ── matchSize ───────────────────────────────────────────────────
#guard matchSize [97, 98, 120, 99, 100] [97, 98, 99, 100] == 2
#guard matchSize [1, 2, 3] [1, 2, 3] == 3
#guard matchSize [7, 8, 9] [1, 2, 3] == 0
#guard matchSize ([] : Sequence) [1, 2] == 0
