import Portion.Impl.Algebra

/-!
# Portion.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in `Impl/Algebra.lean`.

Representation note: `[0, 2)` is `{neg := false, cuts := [0, 2]}`; the ray
`(-∞, 0)` is `{neg := true, cuts := [0]}`; the universe is `{neg := true,
cuts := []}`; the empty set is `{neg := false, cuts := []}`.

DO NOT MODIFY — infrastructure.
-/

open Portion

-- ── contains: half-open membership via toggle parity ────────────
-- [0, 2) = cuts [0,2]: contains 0,1 ; not -1,2,3
#guard contains ⟨false, [0, 2]⟩ 0 == true
#guard contains ⟨false, [0, 2]⟩ 1 == true
#guard contains ⟨false, [0, 2]⟩ 2 == false        -- half-open: 2 excluded
#guard contains ⟨false, [0, 2]⟩ (-1) == false
-- universe / empty
#guard contains ⟨true, []⟩ 99 == true              -- ⊤ contains everything
#guard contains ⟨false, []⟩ 99 == false            -- ∅ contains nothing
-- ray (-∞, 0) = {neg := true, cuts := [0]}: contains -5, not 0
#guard contains ⟨true, [0]⟩ (-5) == true
#guard contains ⟨true, [0]⟩ 0 == false

-- ── complement ──────────────────────────────────────────────────
#guard complement ⟨false, [0, 2]⟩ == ⟨true, [0, 2]⟩
#guard complement ⟨true, []⟩ == ⟨false, []⟩         -- ~⊤ = ∅
-- ~[0,2) contains -1 and 2 but not 0,1
#guard contains (complement ⟨false, [0, 2]⟩) 0 == false
#guard contains (complement ⟨false, [0, 2]⟩) 2 == true

-- ── union: [0,2) | [1,3) = [0,3) ────────────────────────────────
#guard union ⟨false, [0, 2]⟩ ⟨false, [1, 3]⟩ == ⟨false, [0, 3]⟩
-- disjoint [0,1) | [2,3) = both atoms, sorted: cuts [0,1,2,3]
#guard union ⟨false, [0, 1]⟩ ⟨false, [2, 3]⟩ == ⟨false, [0, 1, 2, 3]⟩
#guard union ⟨false, []⟩ ⟨false, [1, 3]⟩ == ⟨false, [1, 3]⟩   -- ∅ | s = s
#guard contains (union ⟨false, [0, 2]⟩ ⟨false, [1, 3]⟩) 2 == true     -- 2 ∈ [0,3)

-- ── intersection: [0,2) & [1,3) = [1,2) ─────────────────────────
#guard intersection ⟨false, [0, 2]⟩ ⟨false, [1, 3]⟩ == ⟨false, [1, 2]⟩
#guard intersection ⟨false, [0, 2]⟩ ⟨false, [3, 4]⟩ == ⟨false, []⟩     -- disjoint = ∅
#guard intersection ⟨true, []⟩ ⟨false, [1, 3]⟩ == ⟨false, [1, 3]⟩      -- ⊤ & s = s

-- ── difference: [0,2) - [1,3) = [0,1) ───────────────────────────
#guard difference ⟨false, [0, 2]⟩ ⟨false, [1, 3]⟩ == ⟨false, [0, 1]⟩
#guard difference ⟨false, [0, 2]⟩ ⟨false, [0, 2]⟩ == ⟨false, []⟩       -- a - a = ∅
#guard contains (difference ⟨false, [0, 2]⟩ ⟨false, [1, 3]⟩) 0 == true
#guard contains (difference ⟨false, [0, 2]⟩ ⟨false, [1, 3]⟩) 1 == false

-- ── isEmpty ─────────────────────────────────────────────────────
#guard isEmpty ⟨false, []⟩ == true
#guard isEmpty ⟨false, [0, 2]⟩ == false
#guard isEmpty ⟨true, []⟩ == false                 -- ⊤ is not empty
#guard isEmpty (intersection ⟨false, [0, 2]⟩ ⟨false, [3, 4]⟩) == true

-- ── literal structure equalities (same DATA, not just same point set) ──
-- a | ~a = ⊤ on the nose; a & ~a = ∅ on the nose
#guard union ⟨false, [0, 2]⟩ (complement ⟨false, [0, 2]⟩) == ⟨true, []⟩
#guard intersection ⟨false, [0, 2]⟩ (complement ⟨false, [0, 2]⟩) == ⟨false, []⟩
-- difference = intersection-with-complement, literally
#guard difference ⟨false, [0, 2]⟩ ⟨false, [1, 3]⟩ == intersection ⟨false, [0, 2]⟩ (complement ⟨false, [1, 3]⟩)
-- commutativity / associativity / De Morgan as identical data
#guard union ⟨false, [0, 2]⟩ ⟨false, [1, 3]⟩ == union ⟨false, [1, 3]⟩ ⟨false, [0, 2]⟩
#guard union (union ⟨false, [0, 1]⟩ ⟨false, [2, 3]⟩) ⟨false, [4, 5]⟩
        == union ⟨false, [0, 1]⟩ (union ⟨false, [2, 3]⟩ ⟨false, [4, 5]⟩)
#guard complement (union ⟨false, [0, 2]⟩ ⟨false, [1, 3]⟩)
        == intersection (complement ⟨false, [0, 2]⟩) (complement ⟨false, [1, 3]⟩)
-- distributivity as identical data
#guard intersection ⟨false, [0, 4]⟩ (union ⟨false, [1, 2]⟩ ⟨false, [3, 5]⟩)
        == union (intersection ⟨false, [0, 4]⟩ ⟨false, [1, 2]⟩) (intersection ⟨false, [0, 4]⟩ ⟨false, [3, 5]⟩)
-- union output is a normalisation fixpoint
#guard union (union ⟨false, [0, 2]⟩ ⟨false, [1, 3]⟩) (union ⟨false, [0, 2]⟩ ⟨false, [1, 3]⟩)
        == union ⟨false, [0, 2]⟩ ⟨false, [1, 3]⟩
