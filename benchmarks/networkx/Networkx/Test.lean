import Networkx.Impl.Components
import Networkx.Impl.Mst

/-!
# Networkx.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in
`Impl/Components.lean` and `Impl/Mst.lean`.

DO NOT MODIFY — infrastructure.
-/

open Networkx

-- ── numConnectedComponents ──────────────────────────────────────
#guard numConnectedComponents ([] : Graph) == 0                       -- no edges
#guard numConnectedComponents [(0, 1, 5)] == 1                        -- one edge, one comp
#guard numConnectedComponents [(0, 1, 5), (1, 2, 3)] == 1             -- chain, one comp
#guard numConnectedComponents [(0, 1, 5), (1, 2, 3), (4, 5, 1)] == 2  -- two comps
#guard numConnectedComponents [(0, 1, 1), (2, 3, 1), (4, 5, 1)] == 3  -- three comps

-- ── sameComponent ───────────────────────────────────────────────
#guard sameComponent [(0, 1, 5), (1, 2, 3)] 0 2 == true               -- transitively connected
#guard sameComponent [(0, 1, 5), (1, 2, 3)] 2 0 == true               -- symmetric
#guard sameComponent [(0, 1, 5), (1, 2, 3), (4, 5, 1)] 0 4 == false   -- different comps
#guard sameComponent [(0, 1, 5)] 0 0 == true                          -- reflexive
#guard sameComponent [(0, 1, 1), (1, 2, 1), (2, 3, 1), (3, 0, 1)] 0 3 == true  -- cycle

-- ── componentOf ─────────────────────────────────────────────────
#guard componentOf [(0, 1, 5), (1, 2, 3)] 0 == [0, 1, 2]              -- sorted reachable set
#guard componentOf [(0, 1, 5), (1, 2, 3), (4, 5, 1)] 4 == [4, 5]      -- the 4-5 component
#guard componentOf [(0, 1, 5)] 3 == [3]                               -- isolated query node

-- ── mstWeight ───────────────────────────────────────────────────
#guard mstWeight ([] : Graph) == 0                                    -- empty
#guard mstWeight [(0, 1, 5)] == 5                                     -- single edge
#guard mstWeight [(0, 1, 1), (1, 2, 2), (0, 2, 3)] == 3               -- triangle: drop heaviest
#guard mstWeight [(0, 1, 1), (1, 2, 2), (3, 4, 7)] == 10              -- forest over two comps
#guard mstWeight [(0, 1, 1), (0, 1, 4)] == 1                          -- parallel: cheaper wins
#guard mstWeight [(0, 1, 10), (1, 2, 10), (0, 2, 1)] == 11            -- pick the cheap shortcut

-- ── numTreeEdges ────────────────────────────────────────────────
#guard numTreeEdges [(0, 1, 1), (1, 2, 2), (0, 2, 3)] == 2            -- 3 nodes − 1 comp
#guard numTreeEdges [(0, 1, 1), (3, 4, 7)] == 2                       -- 4 nodes − 2 comps
#guard numTreeEdges ([] : Graph) == 0                                 -- empty

-- ── subsetWeight ────────────────────────────────────────────────
#guard subsetWeight ([] : Graph) == 0                                 -- empty
#guard subsetWeight [(0, 1, 1), (1, 2, 2)] == 3                       -- sum of weights
#guard subsetWeight [(0, 1, 5), (1, 2, 3), (2, 3, 7)] == 15           -- additive
