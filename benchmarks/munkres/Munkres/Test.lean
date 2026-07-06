import Munkres.Impl.Assign

/-!
# Munkres.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementation in `Impl/Assign.lean`, checked against the `munkres`
library (PyPI `munkres` 1.1.4, `munkres.py`). Every expected value below was
captured from real `munkres` output and cross-checked (in Python) against a
brute-force minimum over **all** column permutations, so each `compute` result
is the genuine Hungarian optimum, not just some feasible assignment.

Cost matrices are modelled as `List (List Nat)`; `compute` returns the optimal
assignment as `(row, column)` pairs. `assignmentCost M pairs` folds the total
cost; `makeCostMatrix` is munkres' profit→cost inversion (`globalMax − value`);
`padMatrix` pads a rectangular matrix to square with `0`.

DO NOT MODIFY — infrastructure.
-/

open Munkres

-- Test matrices (square) with their munkres-verified optimal assignments/costs.
def m1 : List (List Nat) := [[10, 10, 8], [9, 8, 1], [9, 7, 4]]        -- opt cost 18
def m2 : List (List Nat) := [[400, 150, 400], [400, 450, 600], [300, 225, 300]]  -- 850
def m3 : List (List Nat) := [[1, 2], [2, 1]]                            -- 2
def m4 : List (List Nat) := [[0, 1, 2], [1, 0, 2], [2, 1, 0]]          -- 0
def m5 : List (List Nat) := [[5]]                                       -- 5
def m6 : List (List Nat) := [[7, 5, 11], [5, 4, 1], [9, 3, 2]]         -- 11
def m7 : List (List Nat) := [[2, 3, 3], [3, 2, 3], [3, 3, 2]]          -- 6

-- ── compute: exact assignment matches munkres ────────────────────
#guard compute m1 == [(0, 0), (1, 2), (2, 1)]
#guard compute m2 == [(0, 1), (1, 0), (2, 2)]
#guard compute m3 == [(0, 0), (1, 1)]
#guard compute m4 == [(0, 0), (1, 1), (2, 2)]
#guard compute m5 == [(0, 0)]
#guard compute m6 == [(0, 0), (1, 2), (2, 1)]
#guard compute m7 == [(0, 0), (1, 1), (2, 2)]
-- rectangular input: compute pads internally, but only original cells are returned
#guard compute [[1, 2, 3], [4, 5, 6]] == [(0, 0), (1, 1)]

-- ── assignmentCost: total cost of the optimal assignment ─────────
#guard assignmentCost m1 (compute m1) == 18
#guard assignmentCost m2 (compute m2) == 850
#guard assignmentCost m3 (compute m3) == 2
#guard assignmentCost m4 (compute m4) == 0
#guard assignmentCost m5 (compute m5) == 5
#guard assignmentCost m6 (compute m6) == 11
#guard assignmentCost m7 (compute m7) == 6
-- fold pins to a literal sum
#guard assignmentCost m1 [(0, 0), (1, 1), (2, 2)] == 10 + 8 + 4

-- ── padMatrix: rectangular → square, pad value 0 ─────────────────
#guard padMatrix [[1, 2, 3], [4, 5, 6]] == [[1, 2, 3], [4, 5, 6], [0, 0, 0]]
#guard padMatrix [[1], [2], [3]] == [[1, 0, 0], [2, 0, 0], [3, 0, 0]]
#guard padMatrix m1 == m1                       -- already square: unchanged
#guard (padMatrix [[1, 2, 3, 4], [5, 6]]).length == 4    -- side = max(4 cols, 2 rows) = 4
#guard padMatrix [[1, 2, 3, 4], [5, 6]] == [[1, 2, 3, 4], [5, 6, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]

-- ── makeCostMatrix: profit → cost (globalMax − value) ────────────
#guard makeCostMatrix [[5, 3], [2, 7]] == [[2, 4], [5, 0]]
#guard makeCostMatrix [[5, 3, 4], [2, 7, 1], [6, 2, 8]] == [[3, 5, 4], [6, 1, 7], [2, 6, 0]]
#guard makeCostMatrix [[0, 0], [0, 0]] == [[0, 0], [0, 0]]
-- duality: cost-minimizing assignment on makeCostMatrix maximizes profit
#guard (let P := [[5, 3, 4], [2, 7, 1], [6, 2, 8]];
        assignmentCost P (compute (makeCostMatrix P))) == 5 + 7 + 8   -- max profit 20
