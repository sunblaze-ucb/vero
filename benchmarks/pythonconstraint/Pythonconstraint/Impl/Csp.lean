-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Pythonconstraint.Impl.Csp

Finite-domain constraint-satisfaction solver, ported from the `python-constraint`
library (`constraint/__init__.py`, Gustavo Niemeyer, BSD; version 1.4.0). A CSP is
a finite list of variables, each with a finite domain, plus a set of constraints;
the solver enumerates every assignment of domain values to variables that
satisfies all the constraints.

Representation (mathlib-free, all core `Nat`/`List`):
- variables are indices `0 … n-1`;
- `domains : List (List Nat)` — the `i`-th entry is the domain of variable `i`
  (a finite list of candidate values). `domains.length` is the number of
  variables;
- an **assignment** is a `List (Nat × Nat)` (association list `var ↦ value`); the
  solver always emits assignments in **canonical variable-index order**
  (`[(0, v₀), (1, v₁), …, (n-1, v_{n-1})]`), so two assignments are equal exactly
  when they map every variable the same way;
- a `Constraint` is one of the finite-domain predicates supported by
  `python-constraint`: `AllDifferent` (values on its variables pairwise distinct),
  `ExactSum k` (they sum to exactly `k`), `MaxSum k` (sum `≤ k`), `MinSum k`
  (sum `≥ k`), and `InSet s` (each variable's value lies in the set `s`). Each
  constraint carries the list of variables it constrains, mirroring
  python-constraint's `(constraint, variables)` pair.

python-constraint's `BacktrackingSolver` prunes the search with forward-checking
and orders variables by the Degree/MRV heuristics; those choices change the
*order* in which solutions are produced and the *efficiency* of the search, but
never the *set* of solutions (which is what the specifications pin). The faithful
port of the observable behavior is therefore: enumerate the cartesian product of
the domains in variable order and keep the assignments that satisfy every
constraint. `getSolutions` returns them all; `getSolution` returns the first (or
`none`); `solutionCount` is the number found.

All functions are total, terminating `def`s (recursion is structural over the
domain list); no `Float`.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Pythonconstraint

/-- A finite-domain constraint over a list of variables (given by index). Mirrors
    the constraint classes of `python-constraint`. Each constructor carries the
    `vars` it constrains (python-constraint's `variables` argument):
    - `allDifferent vars` — the values at `vars` are pairwise distinct;
    - `exactSum vars k` — the values at `vars` sum to exactly `k`;
    - `maxSum vars k` — the values at `vars` sum to at most `k`;
    - `minSum vars k` — the values at `vars` sum to at least `k`;
    - `inSet vars s` — every variable in `vars` takes a value in the set `s`. -/
inductive Constraint where
  | allDifferent (vars : List Nat)
  | exactSum (vars : List Nat) (k : Nat)
  | maxSum (vars : List Nat) (k : Nat)
  | minSum (vars : List Nat) (k : Nat)
  | inSet (vars : List Nat) (s : List Nat)
deriving Repr, DecidableEq, Inhabited

/-- An assignment: an association list mapping variable indices to values. The
    solver always emits these in ascending variable-index order. -/
abbrev Assignment := List (Nat × Nat)

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `holds c a`: does the complete assignment `a` satisfy constraint `c`? Frozen
    decidable evaluator, mirroring a `python-constraint` constraint's `__call__`
    on a fully assigned tuple. -/
abbrev HoldsSig := Constraint → Assignment → Bool

/-- `getSolutions domains constraints`: every assignment of domain values that
    satisfies all the constraints (the full solution set), in the solver's
    enumeration order. -/
abbrev GetSolutionsSig := List (List Nat) → List Constraint → List Assignment

/-- `getSolution domains constraints`: one satisfying assignment, or `none` if
    the problem is unsatisfiable. -/
abbrev GetSolutionSig := List (List Nat) → List Constraint → Option Assignment

/-- `solutionCount domains constraints`: the number of satisfying assignments. -/
abbrev SolutionCountSig := List (List Nat) → List Constraint → Nat

end Pythonconstraint

-- !benchmark @start global_aux
namespace Pythonconstraint

/-- `lookup a v`: the value assigned to variable `v` in assignment `a`, or `0` if
    absent (assignments passed to `holds` are always complete, so the default is
    never observed on a well-formed call). Frozen helper. -/
def lookup (a : Assignment) (v : Nat) : Nat :=
  match a with
  | [] => 0
  | (v', x) :: rest => if v' = v then x else lookup rest v

/-- `values a vars`: the list of assigned values at the variables `vars`, in order.
    Frozen helper mirroring `[assignments[v] for v in variables]`. -/
def values (a : Assignment) (vars : List Nat) : List Nat :=
  vars.map (lookup a)

/-- `sumList xs`: the sum of a list of `Nat`. Frozen helper. -/
def sumList (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0

/-- `allDistinct xs`: are the elements of `xs` pairwise distinct? Frozen helper —
    the injectivity test underlying `AllDifferent`. -/
def allDistinct : List Nat → Bool
  | [] => true
  | x :: xs => (! xs.contains x) && allDistinct xs

/-- `allInSet xs s`: does every element of `xs` lie in the set `s`? Frozen helper
    underlying `InSet`. -/
def allInSet (xs s : List Nat) : Bool :=
  xs.all (fun x => s.contains x)

end Pythonconstraint
-- !benchmark @end global_aux

namespace Pythonconstraint

-- !benchmark @start code_aux def=holds
-- !benchmark @end code_aux def=holds

def holds : HoldsSig :=
-- !benchmark @start code def=holds
  fun c a =>
    match c with
    | .allDifferent vars => allDistinct (values a vars)
    | .exactSum vars k => sumList (values a vars) == k
    | .maxSum vars k => sumList (values a vars) ≤ k
    | .minSum vars k => k ≤ sumList (values a vars)
    | .inSet vars s => allInSet (values a vars) s
-- !benchmark @end code def=holds

-- !benchmark @start code_aux def=getSolutions
/-- `enumerate domains idx`: all complete assignments of the domains `domains`,
    numbering variables consecutively from `idx`, each in canonical ascending-key
    order (`[(idx, v_idx), (idx+1, …), …]`). Enumerates the full cartesian product
    of the domains in variable order — the discrete analogue of python-constraint's
    exhaustive backtracking search (forward-checking/MRV reorder and prune this
    search but never change its result set). Frozen helper. -/
def enumerate : List (List Nat) → Nat → List Assignment
  | [], _ => [[]]
  | dom :: rest, idx =>
    let tails := enumerate rest (idx + 1)
    dom.flatMap (fun v => tails.map (fun t => (idx, v) :: t))
-- !benchmark @end code_aux def=getSolutions

def getSolutions : GetSolutionsSig :=
-- !benchmark @start code def=getSolutions
  fun domains constraints =>
    match domains with
    | [] => []  -- python-constraint: `Problem.getSolutions` returns [] when there are no variables
    | _ => (enumerate domains 0).filter (fun a => constraints.all (fun c => holds c a))
-- !benchmark @end code def=getSolutions

-- !benchmark @start code_aux def=getSolution
-- !benchmark @end code_aux def=getSolution

def getSolution : GetSolutionSig :=
-- !benchmark @start code def=getSolution
  fun domains constraints => (getSolutions domains constraints).head?
-- !benchmark @end code def=getSolution

-- !benchmark @start code_aux def=solutionCount
-- !benchmark @end code_aux def=solutionCount

def solutionCount : SolutionCountSig :=
-- !benchmark @start code def=solutionCount
  fun domains constraints => (getSolutions domains constraints).length
-- !benchmark @end code def=solutionCount

end Pythonconstraint
