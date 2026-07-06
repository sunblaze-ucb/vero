import PackagingVersion.Impl.Version

/-!
# PackagingVersion.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in `Impl/Version.lean`.

DO NOT MODIFY — infrastructure.
-/

open PackagingVersion

-- abbreviations for readable literals
private def v (e : Nat) (rel : List Nat) (p : PreTag) : Ver := ⟨e, rel, p⟩

-- ── verLe / verEq: epoch dominates ─────────────────────────────
#guard verLe (v 0 [9, 9] .none') (v 1 [0] .none') == true      -- higher epoch wins
#guard verLe (v 1 [0] .none') (v 0 [9, 9] .none') == false

-- ── verLe / verEq: trailing zeros are transparent ──────────────
#guard verEq (v 0 [1] .none') (v 0 [1, 0] .none') == true       -- 1 == 1.0
#guard verEq (v 0 [1] .none') (v 0 [1, 0, 0] .none') == true    -- 1 == 1.0.0
#guard verLe (v 0 [1] .none') (v 0 [1, 0] .none') == true
#guard verEq (v 0 [1, 1] .none') (v 0 [1] .none') == false      -- 1.1 ≠ 1

-- ── verLe: release lexicographic ───────────────────────────────
#guard verLe (v 0 [1, 2] .none') (v 0 [1, 3] .none') == true    -- 1.2 < 1.3
#guard verLe (v 0 [1, 10] .none') (v 0 [1, 2] .none') == false  -- numeric, not lexical

-- ── verLe: tag precedence dev < a < b < rc < final < post ──────
#guard verLe (v 0 [1] (.dev 1)) (v 0 [1] (.a 0)) == true        -- dev < a
#guard verLe (v 0 [1] (.rc 9)) (v 0 [1] .none') == true         -- rc < final
#guard verLe (v 0 [1] .none') (v 0 [1] (.post 0)) == true       -- final < post
#guard verLe (v 0 [1] (.a 1)) (v 0 [1] (.a 2)) == true          -- a1 < a2
#guard verLe (v 0 [1] (.post 0)) (v 0 [1] (.dev 9)) == false    -- post is greatest

-- ── maxVer ─────────────────────────────────────────────────────
#guard maxVer [] == none
#guard maxVer [v 0 [1] .none', v 0 [2] .none', v 0 [1, 5] .none'] == some (v 0 [2] .none')
#guard maxVer [v 0 [1] (.rc 1), v 0 [1] .none', v 0 [1] (.dev 1)] == some (v 0 [1] .none')

-- ── sortVers ───────────────────────────────────────────────────
#guard sortVers [v 0 [2] .none', v 0 [1] .none', v 0 [1, 5] .none']
        == [v 0 [1] .none', v 0 [1, 5] .none', v 0 [2] .none']
#guard sortVers [v 0 [1] .none', v 0 [1] (.dev 0), v 0 [1] (.post 0)]
        == [v 0 [1] (.dev 0), v 0 [1] .none', v 0 [1] (.post 0)]
#guard sortVers ([] : List Ver) == []

-- ── minVer ─────────────────────────────────────────────────────
#guard minVer [] == none
#guard minVer [v 0 [1] .none', v 0 [2] .none', v 0 [1, 5] .none'] == some (v 0 [1] .none')
#guard minVer [v 0 [1] (.rc 1), v 0 [1] .none', v 0 [1] (.dev 1)] == some (v 0 [1] (.dev 1))
#guard minVer [v 1 [0] .none', v 0 [9, 9] .none'] == some (v 0 [9, 9] .none')
