import Pythonconstraint.Impl.Csp

/-!
# Pythonconstraint.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementation in `Impl/Csp.lean`, checked against the
`python-constraint` library (version 1.4.0, `constraint/__init__.py`).

A CSP is `domains : List (List Nat)` (variable `i`'s domain is the `i`-th entry)
plus a list of `Constraint`s. An assignment is a `List (Nat × Nat)` in ascending
variable-index order.

Each oracle solution set below was produced by running python-constraint on the
same problem and normalizing (each solution's items sorted by variable, then the
set of solutions sorted). The reference `getSolutions` here emits solutions in
ascending lexicographic order, which coincides with that normalized form — so the
lists compared below are byte-identical to python-constraint's solution set (the
solver's internal Degree/MRV enumeration order is noncanonical, hence set/count
comparisons are the meaningful checks).

DO NOT MODIFY — infrastructure.
-/

open Pythonconstraint

-- ── holds: constraint evaluator ──────────────────────────────────
-- AllDifferent
#guard holds (.allDifferent [0, 1]) [(0, 1), (1, 2)] == true
#guard holds (.allDifferent [0, 1]) [(0, 2), (1, 2)] == false
#guard holds (.allDifferent [0, 1, 2]) [(0, 1), (1, 2), (2, 3)] == true
#guard holds (.allDifferent [0, 2]) [(0, 1), (1, 2), (2, 1)] == false  -- vars 0,2 both = 1
#guard holds (.allDifferent [0, 2]) [(0, 1), (1, 1), (2, 2)] == true   -- checks only vars 0,2 (1≠2); var 1 ignored
-- ExactSum
#guard holds (.exactSum [0, 1] 3) [(0, 1), (1, 2)] == true
#guard holds (.exactSum [0, 1] 3) [(0, 2), (1, 2)] == false
#guard holds (.exactSum [0, 1, 2] 6) [(0, 1), (1, 2), (2, 3)] == true
-- MaxSum / MinSum / InSet
#guard holds (.maxSum [0, 1] 3) [(0, 1), (1, 2)] == true
#guard holds (.maxSum [0, 1] 3) [(0, 2), (1, 2)] == false
#guard holds (.minSum [0, 1] 3) [(0, 1), (1, 2)] == true
#guard holds (.minSum [0, 1] 3) [(0, 1), (1, 1)] == false
#guard holds (.inSet [0, 1] [1, 3]) [(0, 1), (1, 3)] == true
#guard holds (.inSet [0, 1] [1, 3]) [(0, 1), (1, 2)] == false

-- ── getSolutions: full solution set ──────────────────────────────
-- AllDifferent over [1,2]×[1,2] → the two "swaps"
#guard getSolutions [[1, 2], [1, 2]] [.allDifferent [0, 1]] ==
  [[(0, 1), (1, 2)], [(0, 2), (1, 1)]]
-- ExactSum 5 over [1,2,3]×[1,2,3]
#guard getSolutions [[1, 2, 3], [1, 2, 3]] [.exactSum [0, 1] 5] ==
  [[(0, 2), (1, 3)], [(0, 3), (1, 2)]]
-- ExactSum 4 over [1,2,3]×[1,2,3]
#guard getSolutions [[1, 2, 3], [1, 2, 3]] [.exactSum [0, 1] 4] ==
  [[(0, 1), (1, 3)], [(0, 2), (1, 2)], [(0, 3), (1, 1)]]
-- MaxSum 3 over [1,2]×[1,2]
#guard getSolutions [[1, 2], [1, 2]] [.maxSum [0, 1] 3] ==
  [[(0, 1), (1, 1)], [(0, 1), (1, 2)], [(0, 2), (1, 1)]]
-- MinSum 3 over [1,2]×[1,2]
#guard getSolutions [[1, 2], [1, 2]] [.minSum [0, 1] 3] ==
  [[(0, 1), (1, 2)], [(0, 2), (1, 1)], [(0, 2), (1, 2)]]
-- InSet {1,3} over [1,2,3]×[1,2,3]
#guard getSolutions [[1, 2, 3], [1, 2, 3]] [.inSet [0, 1] [1, 3]] ==
  [[(0, 1), (1, 1)], [(0, 1), (1, 3)], [(0, 3), (1, 1)], [(0, 3), (1, 3)]]
-- AllDifferent on a subset {0,2}; variable 1 is free
#guard getSolutions [[1, 2], [1, 2], [1, 2]] [.allDifferent [0, 2]] ==
  [[(0, 1), (1, 1), (2, 2)], [(0, 1), (1, 2), (2, 2)],
   [(0, 2), (1, 1), (2, 1)], [(0, 2), (1, 2), (2, 1)]]
-- Single variable, single value
#guard getSolutions [[5]] [] == [[(0, 5)]]
-- Unsatisfiable → []
#guard getSolutions [[1], [1]] [.allDifferent [0, 1]] == []
-- No variables → [] (python-constraint boundary)
#guard getSolutions [] [] == []
-- Duplicate domain value → the solution is returned with matching multiplicity
-- (python-constraint does not deduplicate domains): domain [1,1,2] for var 0 yields
-- [(0,1)] twice and [(0,2)] once.
#guard getSolutions [[1, 1, 2], [3]] [] ==
  [[(0, 1), (1, 3)], [(0, 1), (1, 3)], [(0, 2), (1, 3)]]
#guard solutionCount [[1, 1, 2], [3]] [] == 3

-- ── solutionCount ────────────────────────────────────────────────
-- AllDifferent over [1,2,3]³ = 3! permutations
#guard solutionCount [[1, 2, 3], [1, 2, 3], [1, 2, 3]] [.allDifferent [0, 1, 2]] == 6
-- Full product [1,2]³ with no constraints = 2³
#guard solutionCount [[1, 2], [1, 2], [1, 2]] [] == 8
-- Combined AllDifferent + ExactSum 6 over [1,2,3]³ (all 6 perms sum to 6)
#guard solutionCount [[1, 2, 3], [1, 2, 3], [1, 2, 3]]
  [.allDifferent [0, 1, 2], .exactSum [0, 1, 2] 6] == 6
-- MaxSum 3 on {0,1} with a free third variable in [1,2]
#guard solutionCount [[1, 2], [1, 2], [1, 2]] [.maxSum [0, 1] 3] == 6
-- solutionCount agrees with getSolutions length
#guard solutionCount [[1, 2], [1, 2]] [.allDifferent [0, 1]] ==
  (getSolutions [[1, 2], [1, 2]] [.allDifferent [0, 1]]).length

-- ── getSolution: one solution or none ────────────────────────────
-- Satisfiable → the first solution in enumeration order, and it is a real solution
#guard getSolution [[1, 2], [1, 2]] [.allDifferent [0, 1]] == some [(0, 1), (1, 2)]
#guard (getSolution [[1, 2], [1, 2]] [.allDifferent [0, 1]]).isSome == true
-- The returned solution is a member of the full solution set
#guard (getSolutions [[1, 2], [1, 2]] [.allDifferent [0, 1]]).contains
  ((getSolution [[1, 2], [1, 2]] [.allDifferent [0, 1]]).getD []) == true
-- Unsatisfiable → none
#guard getSolution [[1], [1]] [.allDifferent [0, 1]] == none
-- No variables → none
#guard getSolution [] [] == none
