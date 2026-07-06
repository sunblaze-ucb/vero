import Munkres.Harness

/-!
# Munkres.Spec.Assign

Specifications for the assignment-problem core: `compute` (the minimum-cost
assignment), `padMatrix`, `makeCostMatrix`, and `assignmentCost`.

A cost matrix is a `List (List Nat)`, square (n×n) after padding. An assignment
is a **column vector** `p : List Nat` of length `n` that is a permutation of
`[0, n)` — row `i` is assigned column `p[i]`. `compute` returns the assignment as
`(row, column)` pairs; the frozen helper `colVec` reads out its column vector.

The heart of the benchmark is the **two-sided optimality** law, stated over a
frozen *permutation oracle*:
- `perms n` enumerates **every** permutation of `[0, n)` — all `n!` assignments;
- `permCost M p = Σ_i M[i][p[i]]` is the cost of assignment `p`.

`spec_compute_optimal_value` then says: the cost of `compute M` is ≤ the cost of
**every** `p ∈ perms n`. This pins the optimal *value* (the Hungarian optimum)
by a universal quantifier over all `n!` assignments — it is a genuine
no-better-exists statement, not derivable by running `compute`, and cannot be
reward-hacked because the quantifier ranges over the frozen oracle rather than
over the implementation's own output. Ties (several assignments achieving the
minimum) leave the optimal *value* unique even when the optimal witness is not,
so the spec pins the value, never a specific witness.

`makeCostMatrix` duality turns cost-minimization into profit-maximization; the
frozen identity `permCost (makeCostMatrix P) p + permProfit P p = n · globalMax`
witnesses the exact correspondence, and the optimality law then transfers to a
`compute (makeCostMatrix P)` **profit-maximizes** statement over `perms n`.

All helpers here are frozen (`DO NOT MODIFY`) and independent of the scored
`compute` API, so the obligations are stated against genuine combinatorial
semantics.
-/

namespace Munkres

/-!
## Self-contained frozen reference helpers

The cost/optimality laws below are stated against `ref*` helpers defined **entirely
within this Spec file**, deliberately NOT reusing the like-named implementation helpers
(`sumN`, `natGet`, `matGetN`, `maxCols`, `globalMax`) of `Impl/Assign.lean`. Those
implementation helpers live inside agent-editable `!benchmark` slots (`global_aux` /
`code_aux`); in `codeproof` mode the sandbox empties those slots and lets the candidate
re-supply them. If the specifications depended on them, a candidate could redefine
`sumN := fun _ => 0` (making every cost `0`, so the optimality/duality laws hold vacuously
`0 ≤ 0` / `0 + 0 = 0`) or `globalMax := fun _ => 0` (collapsing the duality identity) and
pass without doing the real work. Anchoring the specs to these Spec-local, frozen copies
makes the benchmark non-hackable: the reference cost semantics are fixed no matter what
the candidate supplies for the implementation helpers. Each `ref*` helper is a
byte-for-byte copy of the corresponding frozen `Impl/Assign.lean` helper, so the reference
semantics are identical to the intended ones. The scored APIs (`compute`, `padMatrix`,
`makeCostMatrix`, `assignmentCost`) remain candidate-supplied.
-/

/-- `refNatGet xs i`: the `i`-th element of `xs`, or `0` when out of range. Frozen
    Spec-local copy of `Impl/Assign.natGet`. -/
def refNatGet (xs : List Nat) (i : Nat) : Nat := xs.getD i 0

/-- `refMatGetN M i j`: entry `(i, j)` of a `Nat` matrix, or `0`. Frozen Spec-local copy
    of `Impl/Assign.matGetN`. -/
def refMatGetN (M : List (List Nat)) (i j : Nat) : Nat := refNatGet (M.getD i []) j

/-- `refListMaxN xs`: maximum of a `Nat` list (`0` for the empty list). Frozen Spec-local
    copy of `Impl/Assign.listMaxN` (needed by `refMaxCols` / `refGlobalMax`). -/
def refListMaxN (xs : List Nat) : Nat := xs.foldl Nat.max 0

/-- `refSumN xs`: sum of a `Nat` list. Frozen Spec-local copy of `Impl/Assign.sumN`. -/
def refSumN (xs : List Nat) : Nat := xs.foldl (· + ·) 0

/-- `refMaxCols M`: the widest row length in `M`. Frozen Spec-local copy of
    `Impl/Assign.maxCols`. -/
def refMaxCols (M : List (List Nat)) : Nat := refListMaxN (M.map List.length)

/-- `refGlobalMax M`: the maximum entry over the whole matrix (`0` when empty). Frozen
    Spec-local copy of `Impl/Assign.globalMax`. -/
def refGlobalMax (M : List (List Nat)) : Nat := refListMaxN (M.map refListMaxN)

-- ── Frozen permutation oracle and cost semantics ──────────────

/-- `insertEverywhere x ys`: all lists obtained by inserting `x` into each
    position of `ys`. Frozen helper for `permsAux`. -/
def insertEverywhere (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertEverywhere x ys).map (fun zs => y :: zs)

/-- `permsAux xs`: all permutations of the list `xs`. Frozen helper. -/
def permsAux : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (permsAux xs).flatMap (fun p => insertEverywhere x p)

/-- `perms n`: every permutation of `[0, n)`, as column vectors — the complete
    set of `n!` assignments. Frozen oracle: the universe of feasible assignments
    over which optimality is quantified. -/
def perms (n : Nat) : List (List Nat) := permsAux (List.range n)

/-- `permCost M p`: the cost of the assignment that sends row `i` to column
    `p[i]`, summed over rows — `Σ_i M[i][p[i]]`. Frozen cost semantics,
    independent of the scored `compute`. -/
def permCost (M : List (List Nat)) (p : List Nat) : Nat :=
  refSumN ((List.range p.length).map (fun i => refMatGetN M i (refNatGet p i)))

/-- `permProfit`: identical fold to `permCost`, read as "profit" when `M` is a
    profit matrix. Frozen (an alias kept distinct for readability of the duality
    law). -/
def permProfit (P : List (List Nat)) (p : List Nat) : Nat := permCost P p

/-- `colVec n pairs`: the column vector of an assignment given as `(row, col)`
    pairs — `colVec n pairs [i] =` the column paired with row `i` (or `0` if row
    `i` is unpaired). Frozen reader turning `compute`'s output into a column
    vector for the optimality law. -/
def colVec (n : Nat) (pairs : List (Nat × Nat)) : List Nat :=
  (List.range n).map (fun i =>
    match pairs.find? (fun q => q.1 == i) with
    | some q => q.2
    | none => 0)

/-- `isPermOf n p`: `p` is a permutation of `[0, n)` — it has length `n`, every
    entry is `< n`, and it has no duplicates (equivalently, it hits every value
    in `[0, n)` exactly once). Frozen predicate expressing feasibility. -/
def isPermOf (n : Nat) (p : List Nat) : Prop :=
  p.length = n ∧ (∀ x ∈ p, x < n) ∧ p.Nodup

/-- `minCost M n`: the minimum of `permCost M` over the frozen oracle `perms n` —
    the value of the optimal assignment. Frozen helper (a `foldl min`), used to
    state that `compute` *achieves* the optimum, not merely bounds it. -/
def minCost (M : List (List Nat)) (n : Nat) : Nat :=
  match (perms n).map (permCost M) with
  | [] => 0
  | c :: cs => cs.foldl Nat.min c

/-- `Square M n`: `M` is an n×n matrix with `n ≥ 1` (a nonempty square cost
    matrix, the shape `compute` operates on after padding). Frozen shape
    predicate. -/
def Square (M : List (List Nat)) (n : Nat) : Prop :=
  0 < n ∧ M.length = n ∧ (∀ row ∈ M, row.length = n)

end Munkres

open Munkres

-- ════════════════════════════════════════════════════════════════
-- assignmentCost: the total-cost fold
-- ════════════════════════════════════════════════════════════════

/-- `assignmentCost` is exactly the sum of `M[r][c]` over the assignment pairs.
    Pins the total-cost fold to the frozen entry lookup `refMatGetN` and `refSumN`
    (a max-fold, a product, or dropping/counting pairs all fail). General over
    every matrix and every list of pairs. Over `impl.munkres.assignmentCost`. -/
def spec_assignmentCost_fold (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (pairs : List (Nat × Nat)),
    impl.munkres.assignmentCost M pairs = refSumN (pairs.map (fun p => refMatGetN M p.1 p.2))

-- ════════════════════════════════════════════════════════════════
-- padMatrix: rectangular → square (pad with 0)
-- ════════════════════════════════════════════════════════════════

/-- `padMatrix` always returns a **square** matrix: its side length is
    `max (widest row) (#rows)`, every output row has that length, and there are
    exactly that many rows. Pins padding to the true square shape (a no-op, a
    row-only pad, or a column-only pad all fail). Over `impl.munkres.padMatrix`,
    `refMaxCols`. -/
def spec_pad_square (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)),
    let n := Nat.max (refMaxCols M) M.length
    (impl.munkres.padMatrix M).length = n ∧
    (∀ row ∈ impl.munkres.padMatrix M, row.length = n)

/-- `padMatrix` is the identity on matrices that are **already square** — padding
    an n×n matrix returns it unchanged, so the optimal assignment (hence its
    cost) is untouched. Pins padding to preserve square input exactly (a variant
    that always appends a row/column, or reorders, fails). Over
    `impl.munkres.padMatrix`, `Square`. -/
def spec_pad_square_id (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (n : Nat), Square M n → impl.munkres.padMatrix M = M

-- ════════════════════════════════════════════════════════════════
-- makeCostMatrix: profit → cost, and the duality identity
-- ════════════════════════════════════════════════════════════════

/-- `makeCostMatrix` inverts each entry as `globalMax P − value`: entry `(i, j)`
    of the result is `refGlobalMax P − P[i][j]`, for every in-range cell. Pins the
    transform to munkres' default `inversion_function` (a plain copy, a negation,
    or a row-local `max − v` all fail). Over `impl.munkres.makeCostMatrix`,
    `refGlobalMax`, `refMatGetN`. -/
def spec_makeCost_entrywise (impl : RepoImpl) : Prop :=
  ∀ (P : List (List Nat)) (i j : Nat),
    i < P.length → j < (P.getD i []).length →
      refMatGetN (impl.munkres.makeCostMatrix P) i j = refGlobalMax P - refMatGetN P i j

/-- Duality identity: for a square profit matrix `P` and **any** assignment `p`
    over `perms n`, the cost of `p` under `makeCostMatrix P` plus the profit of
    `p` under `P` is the constant `n · globalMax P`. This is the exact
    profit↔cost correspondence that makes cost-minimization equal to
    profit-maximization; because the sum is constant across all `p`, minimizing
    cost maximizes profit. Over `impl.munkres.makeCostMatrix`, `permCost`,
    `permProfit`, `refGlobalMax`, `perms`, `Square`. -/
def spec_makeCost_duality (impl : RepoImpl) : Prop :=
  ∀ (P : List (List Nat)) (n : Nat), Square P n →
    ∀ p ∈ perms n,
      permCost (impl.munkres.makeCostMatrix P) p + permProfit P p = n * refGlobalMax P

-- ════════════════════════════════════════════════════════════════
-- compute: feasibility (bijection) + two-sided optimality (headline)
-- ════════════════════════════════════════════════════════════════

/-- Feasibility — `compute` returns a **bijection**: for a square matrix, its
    output is exactly one pair per row `0 … n-1` (first coordinates are `[0, n)`
    in order), and the chosen columns form a permutation of `[0, n)`. This is the
    combinatorial well-formedness of an assignment (each row once, each column
    once). Pins `compute` to a genuine one-to-one matching, defeating any hack
    that returns fewer pairs, repeats a column, or assigns off-diagonal garbage.
    Over `impl.munkres.compute`, `colVec`, `isPermOf`, `Square`. -/
def spec_compute_feasible (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (n : Nat), Square M n →
    (impl.munkres.compute M).map Prod.fst = List.range n ∧
    isPermOf n (colVec n (impl.munkres.compute M))

/-- Assignment lies in the oracle: for a square matrix, the column vector of
    `compute M` is one of the enumerated permutations, `colVec n (compute M) ∈
    perms n`. This makes the link between `compute`'s output and the optimality
    oracle explicit — the returned assignment is genuinely among the `n!`
    candidates the optimum is quantified over, so the ≤-law and the achieves-min
    equality really are statements about `compute`'s own assignment. Over
    `impl.munkres.compute`, `colVec`, `perms`, `Square`. -/
def spec_compute_colVec_mem (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (n : Nat), Square M n →
    colVec n (impl.munkres.compute M) ∈ perms n

/-- Optimality (no-better-exists) — the **crown** law. For a square matrix, the
    cost of `compute M` is ≤ the cost of **every** assignment `p` in the frozen
    oracle `perms n`. The quantifier ranges over all `n!` permutations, so this
    is a true global-minimum statement (the Hungarian optimum), independent of
    the implementation's own output. It pins the optimal *value*: any assignment
    achieving a strictly smaller cost would refute it, and no greedy / local /
    row-min heuristic can satisfy it in general. Non-hackable — `perms` is
    frozen. Over `impl.munkres.compute`, `assignmentCost`, `permCost`, `perms`,
    `Square`. -/
def spec_compute_optimal_value (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (n : Nat), Square M n →
    ∀ p ∈ perms n,
      impl.munkres.assignmentCost M (impl.munkres.compute M) ≤ permCost M p

/-- Optimality achieved — `compute`'s cost **equals** the minimum over the frozen
    oracle, `assignmentCost M (compute M) = minCost M n`. Together with
    `spec_compute_optimal_value` (the ≤ direction) this makes `compute` attain
    the exact optimal value: it is not merely a lower bound but the realized
    minimum. Because ties keep the *value* unique, this is well-posed even when
    the optimal witness is not. Over `impl.munkres.compute`,
    `impl.munkres.assignmentCost`, `minCost`, `perms`, `Square`. -/
def spec_compute_achieves_min (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (n : Nat), Square M n →
    impl.munkres.assignmentCost M (impl.munkres.compute M) = minCost M n

/-- Cost read-out consistency: for a square matrix, the total cost of `compute M`
    (via `assignmentCost`) equals the `permCost` of its own column vector — the
    two cost views agree. Ties the `(row, col)`-pair fold to the column-vector
    fold used by the optimality laws, so the optimum stated over `perms` really
    is the assignment `compute` returns. Over `impl.munkres.compute`,
    `impl.munkres.assignmentCost`, `permCost`, `colVec`, `Square`. -/
def spec_compute_cost_colVec (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (n : Nat), Square M n →
    impl.munkres.assignmentCost M (impl.munkres.compute M)
      = permCost M (colVec n (impl.munkres.compute M))

/-- Profit-maximization via duality — the payoff of `makeCostMatrix`. For a
    square profit matrix `P`, the assignment `compute` finds on the cost matrix
    `makeCostMatrix P` has profit (under `P`) ≥ the profit of **every**
    assignment in `perms n`. So minimizing the inverted cost maximizes the
    original profit, over all `n!` assignments. This is the two-sided optimality
    law transported through the duality identity; it is the reason `make_cost_matrix`
    exists. Over `impl.munkres.compute`, `impl.munkres.makeCostMatrix`,
    `permProfit`, `colVec`, `perms`, `Square`. -/
def spec_compute_profit_max (impl : RepoImpl) : Prop :=
  ∀ (P : List (List Nat)) (n : Nat), Square P n →
    ∀ p ∈ perms n,
      permProfit P p
        ≤ permProfit P (colVec n (impl.munkres.compute (impl.munkres.makeCostMatrix P)))

-- ════════════════════════════════════════════════════════════════
-- Optimal value: uniqueness, achievement, and dual characterization
-- ════════════════════════════════════════════════════════════════

/-- The optimal value `minCost M n` is the **unique** value `v` that is both a
    lower bound on the cost of every assignment in `perms n` and attained by some
    assignment: `v = minCost M n` iff (`v ≤ permCost M p` for all `p ∈ perms n`)
    and (`permCost M p = v` for some `p ∈ perms n`). Pins the optimum as the
    least attained cost — no strictly smaller value is a lower bound, and every
    lower value fails to be attained. Over `perms`, `permCost`, `minCost`,
    `Square`. -/
def spec_minCost_unique_value (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (n : Nat), Square M n →
    ∀ v : Nat,
      (((∀ p ∈ perms n, v ≤ permCost M p) ∧
          (∃ p, p ∈ perms n ∧ permCost M p = v)) ↔
        v = minCost M n)

/-- Any assignment attaining the optimal cost is globally optimal: if
    `permCost M p = minCost M n` for `p ∈ perms n`, then `permCost M p ≤
    permCost M q` for **every** `q ∈ perms n`. Pins the equivalence between
    attaining `minCost` and being a cost-minimizer over the whole oracle. Over
    `perms`, `permCost`, `minCost`, `Square`. -/
def spec_minCost_witness_optimal (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (n : Nat) (p : List Nat),
    Square M n → p ∈ perms n → permCost M p = minCost M n →
      ∀ q ∈ perms n, permCost M p ≤ permCost M q

-- ════════════════════════════════════════════════════════════════
-- Structural cost laws: reduction-shift, monotonicity, trace, extensionality
-- ════════════════════════════════════════════════════════════════

/-- Row-constant subtraction shifts every assignment's cost by exactly that
    constant. For a square `M`, a row `r < n`, and a constant `c` with
    `c ≤ M[r][j]` for every column `j`, subtracting `c` from every entry of row
    `r` decreases `permCost` of **each** `p ∈ perms n` by `c`:
    `permCost R p + c = permCost M p`, where `R` is `M` with row `r` reduced by
    `c`. Pins the primal-dual reduction invariant — the assignment ranking is
    preserved because every assignment uses row `r` exactly once. Over `perms`,
    `permCost`, `refMatGetN`, `Square`. -/
def spec_permCost_row_reduction_shift (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (n r c : Nat) (p : List Nat),
    Square M n → r < n → p ∈ perms n →
      (∀ j, j < n → c ≤ refMatGetN M r j) →
        let R := (List.range n).map (fun i =>
          (List.range n).map (fun j =>
            if i == r then refMatGetN M i j - c else refMatGetN M i j))
        permCost R p + c = permCost M p

/-- Row-constant subtraction shifts the optimal value by that same constant. For
    a square `M`, row `r < n`, and `c ≤ M[r][j]` for every `j`,
    `minCost R n + c = minCost M n`, where `R` reduces row `r` of `M` by `c`.
    Pins that row reduction leaves the optimal assignment set unchanged (only the
    optimal value is offset). Over `minCost`, `refMatGetN`, `Square`. -/
def spec_row_reduction_minCost_shift (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (n r c : Nat),
    Square M n → r < n →
      (∀ j, j < n → c ≤ refMatGetN M r j) →
        let R := (List.range n).map (fun i =>
          (List.range n).map (fun j =>
            if i == r then refMatGetN M i j - c else refMatGetN M i j))
        minCost R n + c = minCost M n

/-- The optimal value is monotone in the cost entries: if `M ≤ M'` entrywise on
    the `n × n` grid then `minCost M n ≤ minCost M' n`. Pins that raising costs
    can never lower the optimum. Over `minCost`, `refMatGetN`, `Square`. -/
def spec_minCost_monotone_entrywise (impl : RepoImpl) : Prop :=
  ∀ (M M' : List (List Nat)) (n : Nat),
    Square M n → Square M' n →
      (∀ i j, i < n → j < n → refMatGetN M i j ≤ refMatGetN M' i j) →
        minCost M n ≤ minCost M' n

/-- The identity assignment costs the diagonal trace: for a square `M`,
    `permCost M (range n) = Σ_i M[i][i]`. Pins the cost of the identity
    permutation to the sum of diagonal entries. Over `permCost`, `refSumN`,
    `refMatGetN`, `Square`. -/
def spec_permCost_identity_trace (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (n : Nat), Square M n →
    permCost M (List.range n) =
      refSumN ((List.range n).map (fun i => refMatGetN M i i))

/-- An assignment's cost depends only on the `n` cells it selects: if `M` and
    `M'` agree on every selected cell `(i, p[i])` for `i < n`, then
    `permCost M p = permCost M' p` for `p ∈ perms n`. Pins that unselected
    entries are irrelevant to an assignment's cost. Over `perms`, `permCost`,
    `refMatGetN`, `refNatGet`. -/
def spec_permCost_extensional (impl : RepoImpl) : Prop :=
  ∀ (M M' : List (List Nat)) (n : Nat) (p : List Nat), p ∈ perms n →
    (∀ i, i < n → refMatGetN M i (refNatGet p i) = refMatGetN M' i (refNatGet p i)) →
      permCost M p = permCost M' p

/-- `compute`'s realized cost is sandwiched between the optimum and the trivial
    upper bound: for a square `M`, `minCost M n ≤ assignmentCost M (compute M) ≤
    n · globalMax M`. Pins the returned assignment's total cost between the
    Hungarian optimum and `n` times the largest entry. Over
    `impl.munkres.compute`, `impl.munkres.assignmentCost`, `minCost`,
    `refGlobalMax`, `Square`. -/
def spec_compute_cost_global_bounds (impl : RepoImpl) : Prop :=
  ∀ (M : List (List Nat)) (n : Nat), Square M n →
    minCost M n ≤ impl.munkres.assignmentCost M (impl.munkres.compute M) ∧
    impl.munkres.assignmentCost M (impl.munkres.compute M) ≤ n * refGlobalMax M
