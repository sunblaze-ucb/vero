import Dijkstar.Impl.ShortestPath

/-!
# Dijkstar.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in
`Impl/ShortestPath.lean`.

DO NOT MODIFY — infrastructure.
-/

open Dijkstar

-- ── edgeWeight ──────────────────────────────────────────────────
#guard edgeWeight [(0, 1, 5), (1, 2, 3)] 0 1 == some 5
#guard edgeWeight [(0, 1, 5), (1, 2, 3)] 0 2 == none           -- no direct edge
#guard edgeWeight [(0, 1, 5), (0, 1, 3)] 0 1 == some 5         -- first match wins
#guard edgeWeight ([] : Graph) 0 1 == none

-- ── findPathCost: shortest cost through intermediates ──
-- direct edge 0→2 costs 100, but 0→1→2 costs 5+3 = 8; the shorter wins.
#guard findPathCost [(0, 1, 5), (1, 2, 3), (0, 2, 100)] 0 2 == some 8
#guard findPathCost [(0, 1, 1), (1, 2, 1), (0, 2, 5)] 0 2 == some 2
#guard findPathCost [(0, 1, 5)] 0 0 == some 0                  -- self: zero cost
#guard findPathCost [(0, 1, 5)] 0 2 == none                    -- unreachable
#guard findPathCost ([] : Graph) 3 3 == some 0                 -- self always 0
-- a longer chain still yields the cheaper multi-hop cost:
#guard findPathCost [(0, 1, 2), (1, 2, 2), (2, 3, 2), (0, 3, 10)] 0 3 == some 6

-- ── reachable ───────────────────────────────────────────────────
#guard reachable [(0, 1, 5), (1, 2, 3)] 0 2 == true
#guard reachable [(0, 1, 5)] 0 2 == false
#guard reachable [(0, 1, 5)] 0 0 == true                       -- self reachable
#guard reachable ([] : Graph) 7 7 == true
