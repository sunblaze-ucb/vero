import Semver.Impl.Version

/-!
# Semver.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in `Impl/Version.lean`.

DO NOT MODIFY — infrastructure.
-/

open Semver

-- abbreviations for readable literals
private def v (mj mn pa : Nat) (pre : List Ident) (build : List String) : Version :=
  ⟨mj, mn, pa, pre, build⟩

-- ── compareV / lt / eq: core precedence ────────────────────────
#guard versionLt (v 1 0 0 [] []) (v 2 0 0 [] []) == true            -- major
#guard versionLt (v 1 0 0 [] []) (v 1 1 0 [] []) == true            -- minor
#guard versionLt (v 1 0 0 [] []) (v 1 0 1 [] []) == true            -- patch
#guard versionLt (v 1 0 10 [] []) (v 1 0 2 [] []) == false          -- numeric, not lexical

-- ── lt / eq: pre-release lowers precedence ─────────────────────
#guard versionLt (v 1 0 0 [.alpha "alpha"] []) (v 1 0 0 [] []) == true   -- pre < release
#guard versionLt (v 1 0 0 [] []) (v 1 0 0 [.alpha "alpha"] []) == false
#guard versionEq (v 1 0 0 [.alpha "rc"] []) (v 1 0 0 [] []) == false

-- ── lt: pre-release identifier rules ───────────────────────────
#guard versionLt (v 1 0 0 [.num 1] []) (v 1 0 0 [.alpha "x"] []) == true      -- numeric < alpha
#guard versionLt (v 1 0 0 [.alpha "alpha"] []) (v 1 0 0 [.alpha "beta"] []) == true  -- ascii
#guard versionLt (v 1 0 0 [.alpha "beta", .num 2] []) (v 1 0 0 [.alpha "beta", .num 11] []) == true -- numeric cmp
#guard versionLt (v 1 0 0 [.alpha "alpha"] []) (v 1 0 0 [.alpha "alpha", .num 1] []) == true -- longer wins

-- ── eq / compareV: build metadata ignored ──────────────────────
#guard versionEq (v 1 0 0 [] ["build", "1"]) (v 1 0 0 [] ["build", "2"]) == true
#guard versionEq (v 1 0 0 [.alpha "rc", .num 1] ["x"]) (v 1 0 0 [.alpha "rc", .num 1] []) == true
#guard compareV (v 1 0 0 [] ["a"]) (v 1 0 0 [] ["b"]) == Ordering.eq

-- ── satisfies ──────────────────────────────────────────────────
#guard satisfies [] (v 1 0 0 [] []) == true
#guard satisfies [⟨.ge, v 1 0 0 [] []⟩] (v 1 2 0 [] []) == true
#guard satisfies [⟨.ge, v 1 0 0 [] []⟩] (v 0 9 0 [] []) == false
#guard satisfies [⟨.ge, v 1 0 0 [] []⟩, ⟨.lt, v 2 0 0 [] []⟩] (v 1 5 0 [] []) == true
#guard satisfies [⟨.ge, v 1 0 0 [] []⟩, ⟨.lt, v 2 0 0 [] []⟩] (v 2 0 0 [] []) == false

-- ── select: greatest matching version ──────────────────────────
#guard select [⟨.ge, v 1 0 0 [] []⟩, ⟨.lt, v 2 0 0 [] []⟩]
        [v 1 0 0 [] [], v 1 5 0 [] [], v 1 2 0 [] [], v 2 0 0 [] []]
        == some (v 1 5 0 [] [])
#guard select [] ([] : List Version) == none
#guard select [⟨.ge, v 3 0 0 [] []⟩]
        [v 1 0 0 [] [], v 2 0 0 [] []]
        == none
#guard select [⟨.lt, v 2 0 0 [] []⟩]
        [v 1 0 0 [.alpha "rc"] [], v 1 0 0 [] [], v 1 0 0 [.alpha "alpha"] []]
        == some (v 1 0 0 [] [])     -- normal release beats its pre-releases
