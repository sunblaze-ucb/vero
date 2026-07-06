import Munkres.Impl.Assign
import Munkres.Bundle
import Munkres.Harness
import Munkres.Spec.Assign
import Munkres.Test

/-!
# Munkres

Root import hub: the Munkres / Hungarian / Kuhn–Munkres algorithm for the
classical **assignment problem**, ported from the `munkres` library (PyPI
`munkres`, bmc/munkres, Apache-2.0, `munkres.py`). Given an n×n integer cost
matrix, `compute` finds an assignment (a one row → one column bijection) of
minimum total cost. A cost matrix is modelled mathlib-free as
`List (List Nat)`; the algorithm's mutable working state (the reduced matrix,
covers, and star/prime marks) is threaded functionally through a fuel-bounded
step machine.

Assignment core (`Impl/Assign`, `Spec/Assign`): `padMatrix` (rectangular →
square, pad `0`), `makeCostMatrix` (profit → cost via `globalMax − value`,
munkres' default inversion), `compute` (the optimal assignment as `(row, col)`
pairs), and `assignmentCost` (the total-cost fold).

The behaviour is pinned by `Spec/Assign.lean`. The headline obligations are the
**two-sided optimality** laws stated over a frozen permutation oracle: `compute`
returns a genuine bijection (`spec_compute_feasible`), and its cost is ≤ the cost
of **every** one of the `n!` assignments in `perms n`
(`spec_compute_optimal_value`) — indeed it *achieves* the exact minimum
(`spec_compute_achieves_min`). Duality (`spec_makeCost_duality`,
`spec_compute_profit_max`) turns cost-minimization into profit-maximization, and
`spec_pad_square` / `spec_pad_square_id` pin the padding shape and its identity
on square input. Everything is discrete `Nat`/`Int`/`List`; no `Float`.
-/
