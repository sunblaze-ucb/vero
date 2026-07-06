import Pythonconstraint.Harness

/-!
# Pythonconstraint.Spec.Csp

Specifications for the finite-domain CSP solver: `getSolutions` (the full
solution set), `getSolution` (one solution / none), `solutionCount`, and the
frozen constraint evaluator `holds`.

A CSP is `domains : List (List Nat)` (variable `i`'s domain is the `i`-th entry)
plus `constraints : List Constraint`. An assignment is a `List (Nat × Nat)`
(`var ↦ value`) emitted by the solver in canonical ascending-key order.

The specifications are stated against frozen *reference* predicates that are
deliberately independent of the scored APIs, built only from the **Spec-local**
frozen helpers defined in this file (`refEnumerate`, `refLookup`, `refValues`,
`refSumList`, `refAllDistinct`, `refAllInSet`) — never the implementation helpers,
which live in agent-editable `!benchmark` slots (see the "self-contained frozen
reference helpers" note below). The soundness / completeness obligations thus pin
the solver against fixed genuine semantics rather than against the implementation
under test:

- `respectsDomains doms a` — `a` is a *complete, canonically-ordered* assignment
  of the domains `doms`: it is exactly one of the cartesian-product tuples
  enumerated by the frozen `refEnumerate`. This is the domain-legality predicate.
- `holdsRef c a` — the reference meaning of a single constraint on a complete
  assignment, mirroring `holds` but rebuilt from the Spec-local frozen helpers.
- `satisfiesRef cs a` — every constraint in `cs` holds of `a` (via `holdsRef`).
- `modelMember doms cs a` — `a` is a legal, all-constraints-satisfying assignment
  (`respectsDomains doms a ∧ satisfiesRef cs a`): membership in the **full model
  set**.

The crown laws state that the solver's returned list is **exactly** the model
set (soundness + completeness), order-independently. `getSolution`,
`solutionCount` and the constraint-semantics laws round out the cross-API and
frozen-predicate anchoring.

DO NOT MODIFY.
-/

namespace Pythonconstraint

/-!
## Self-contained frozen reference helpers

The reference predicates below are rebuilt from `ref*` helpers defined **entirely
within this Spec file**, deliberately NOT reusing the implementation helpers
(`lookup`, `values`, `enumerate`, …) from `Impl/Csp.lean`. Those implementation
helpers live inside agent-editable `!benchmark` slots (`global_aux` / `code_aux`);
in `codeproof` mode the sandbox empties those slots and lets the candidate
re-supply them. If the specifications depended on them, a candidate could redefine
`enumerate := fun _ _ => []` (making the reference model set empty) and pass every
solution law vacuously. Anchoring the specs to these Spec-local, frozen copies
makes the benchmark non-hackable: the reference semantics are fixed no matter what
the candidate supplies for the implementation helpers.
-/

/-- `refLookup a v`: value assigned to variable `v` in `a`, or `0` if absent.
    Frozen Spec-local copy. -/
def refLookup (a : Assignment) (v : Nat) : Nat :=
  match a with
  | [] => 0
  | (v', x) :: rest => if v' = v then x else refLookup rest v

/-- `refValues a vars`: assigned values at `vars`, in order. Frozen Spec-local copy. -/
def refValues (a : Assignment) (vars : List Nat) : List Nat :=
  vars.map (refLookup a)

/-- `refSumList xs`: sum of a `Nat` list. Frozen Spec-local copy. -/
def refSumList (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0

/-- `refAllDistinct xs`: are the elements of `xs` pairwise distinct? Frozen
    Spec-local copy — the injectivity test underlying `AllDifferent`. -/
def refAllDistinct : List Nat → Bool
  | [] => true
  | x :: xs => (! xs.contains x) && refAllDistinct xs

/-- `refAllInSet xs s`: does every element of `xs` lie in `s`? Frozen Spec-local
    copy underlying `InSet`. -/
def refAllInSet (xs s : List Nat) : Bool :=
  xs.all (fun x => s.contains x)

/-- `refEnumerate doms idx`: the full cartesian product of the domains `doms`,
    variables numbered from `idx`, each assignment in canonical ascending-key
    order. Frozen Spec-local copy of the reference enumeration — this is the
    domain product against which soundness/completeness/multiplicity are stated. -/
def refEnumerate : List (List Nat) → Nat → List Assignment
  | [], _ => [[]]
  | dom :: rest, idx =>
    let tails := refEnumerate rest (idx + 1)
    dom.flatMap (fun v => tails.map (fun t => (idx, v) :: t))

/-- `respectsDomains doms a`: `a` is a complete, canonically-ordered assignment of
    the domains `doms` — there is at least one variable (`doms ≠ []`) and `a` is
    exactly one of the tuples enumerated by the frozen `refEnumerate` (variables
    `0 … n-1`, keys ascending, each value drawn from the matching domain). The
    `doms ≠ []` guard faithfully mirrors python-constraint's `Problem`, which
    treats a problem with no variables as having no solutions (`getSolutions`
    returns `[]`) rather than the single empty assignment. Frozen domain-legality
    predicate, independent of the scored APIs. -/
def respectsDomains (doms : List (List Nat)) (a : Assignment) : Prop :=
  doms ≠ [] ∧ a ∈ refEnumerate doms 0

/-- `holdsRef c a`: the reference semantics of a single constraint on a complete
    assignment, rebuilt from the frozen Spec-local helpers (independent of the
    scored `holds` API). Frozen predicate. -/
def holdsRef (c : Constraint) (a : Assignment) : Bool :=
  match c with
  | .allDifferent vars => refAllDistinct (refValues a vars)
  | .exactSum vars k => refSumList (refValues a vars) == k
  | .maxSum vars k => refSumList (refValues a vars) ≤ k
  | .minSum vars k => k ≤ refSumList (refValues a vars)
  | .inSet vars s => refAllInSet (refValues a vars) s

/-- `satisfiesRef cs a`: every constraint in `cs` holds of the complete assignment
    `a`, by the reference semantics `holdsRef`. Frozen predicate. -/
def satisfiesRef (cs : List Constraint) (a : Assignment) : Prop :=
  ∀ c ∈ cs, holdsRef c a = true

/-- `modelMember doms cs a`: `a` is in the **full model set** of the CSP — a
    complete, domain-respecting assignment satisfying every constraint. This is
    the reference specification of a solution, independent of the solver. Frozen
    predicate. -/
def modelMember (doms : List (List Nat)) (cs : List Constraint) (a : Assignment) : Prop :=
  respectsDomains doms a ∧ satisfiesRef cs a

/-- `modelList doms cs`: the reference **model list** — the frozen cartesian-product
    enumeration filtered by the reference constraint semantics (`[]` when there are
    no variables, mirroring python-constraint). A genuine multiset-level reference
    (it preserves the multiplicity a duplicated domain value induces), built only
    from frozen Spec-local helpers and independent of the scored APIs. Frozen
    helper used to state the strongest correctness law as a permutation. -/
def modelList (doms : List (List Nat)) (cs : List Constraint) : List Assignment :=
  match doms with
  | [] => []
  | _ => (refEnumerate doms 0).filter (fun a => cs.all (fun c => holdsRef c a))

/-- `refDomainProduct doms`: the product of the domain-list lengths (`∏ dᵢ.length`,
    the empty product being `1`). Frozen Spec-local helper — the cardinality of the
    cartesian product `refEnumerate` enumerates. -/
def refDomainProduct : List (List Nat) → Nat
  | [] => 1
  | d :: ds => d.length * refDomainProduct ds

/-- `refFilterDomainAt doms i allowed`: `doms` with the `i`-th domain replaced by its
    sublist of values contained in `allowed`, other domains unchanged (out-of-range
    `i` leaves `doms` unchanged). Frozen Spec-local helper — the domain-pruning
    operation of forward-checking a unary membership restriction on variable `i`. -/
def refFilterDomainAt : List (List Nat) → Nat → List Nat → List (List Nat)
  | [], _, _ => []
  | d :: rest, 0, allowed => d.filter (fun x => allowed.contains x) :: rest
  | d :: rest, n + 1, allowed => d :: refFilterDomainAt rest n allowed

/-- `refKeys a`: the variable indices (first components) of an assignment, in order.
    Frozen Spec-local helper. -/
def refKeys (a : Assignment) : List Nat :=
  a.map (fun p => p.1)

/-- `refDomainAt doms i`: the domain of variable `i` (the `i`-th entry of `doms`, or
    `[]` if out of range). Frozen Spec-local helper. -/
def refDomainAt : List (List Nat) → Nat → List Nat
  | [], _ => []
  | d :: _, 0 => d
  | _ :: rest, n + 1 => refDomainAt rest n

/-- `refDomainsOfVars doms vars`: the concatenation of the domains of the variables
    `vars`, in order. Frozen Spec-local helper — the pool of values the variables
    `vars` can jointly take. -/
def refDomainsOfVars (doms : List (List Nat)) (vars : List Nat) : List Nat :=
  vars.foldr (fun v acc => refDomainAt doms v ++ acc) []

/-- `refDedup xs`: `xs` with duplicates removed (keeping the last occurrence's
    position). Frozen Spec-local helper — `refDedup xs |>.length` is the number of
    distinct values in `xs`. -/
def refDedup : List Nat → List Nat
  | [] => []
  | x :: xs => if xs.contains x then refDedup xs else x :: refDedup xs

end Pythonconstraint

open Pythonconstraint

-- ════════════════════════════════════════════════════════════════
-- holds: constraint semantics anchored to frozen predicates
-- ════════════════════════════════════════════════════════════════

/-- `AllDifferent` ⟺ injectivity: for any assignment and variable list,
    `holds (AllDifferent vars) a` is `true` exactly when the values assigned to
    `vars` are pairwise distinct — the injectivity of the assignment restricted to
    `vars`. Pins `AllDifferent` to the genuine frozen `refAllDistinct` predicate (a
    constraint that always passes, or one that only checks adjacent pairs, fails).
    Over `impl.pythonconstraint.holds`, `refValues`, `refAllDistinct`. -/
def spec_alldiff_iff (impl : RepoImpl) : Prop :=
  ∀ (vars : List Nat) (a : Assignment),
    impl.pythonconstraint.holds (.allDifferent vars) a = refAllDistinct (refValues a vars)

/-- `ExactSum k` ⟺ Σ = k: for any assignment and variable list,
    `holds (ExactSum vars k) a` is `true` exactly when the values assigned to
    `vars` sum to exactly `k`. Pins `ExactSum` to the frozen `refSumList` predicate
    (a `≤ k` or `≥ k` reading fails). Over `impl.pythonconstraint.holds`,
    `refValues`, `refSumList`. -/
def spec_exactsum_iff (impl : RepoImpl) : Prop :=
  ∀ (vars : List Nat) (k : Nat) (a : Assignment),
    impl.pythonconstraint.holds (.exactSum vars k) a = (refSumList (refValues a vars) == k)

/-- `MaxSum k` ⟺ Σ ≤ k, `MinSum k` ⟺ Σ ≥ k, `InSet s` ⟺ every value ∈ s: the
    remaining constraint kinds are each pinned to their frozen predicate. Ties the
    whole `holds` evaluator to the reference `holdsRef` for every constructor. Over
    `impl.pythonconstraint.holds`, `holdsRef`. -/
def spec_holds_ref (impl : RepoImpl) : Prop :=
  ∀ (c : Constraint) (a : Assignment),
    impl.pythonconstraint.holds c a = holdsRef c a

-- ════════════════════════════════════════════════════════════════
-- getSolutions: soundness (every returned assignment is a real solution)
-- ════════════════════════════════════════════════════════════════

/-- Soundness: every assignment returned by `getSolutions` is a genuine solution —
    it is a complete, domain-respecting assignment (`respectsDomains`) that
    satisfies **every** constraint (`satisfiesRef`, the reference semantics). No
    spurious, domain-violating, or constraint-violating assignment is ever
    returned. Stated against the frozen reference predicates, so it cannot be
    satisfied by a solver that also games `holds`. Over
    `impl.pythonconstraint.getSolutions`, `modelMember`, `respectsDomains`,
    `satisfiesRef`. -/
def spec_solutions_sound (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (cs : List Constraint) (a : Assignment),
    a ∈ impl.pythonconstraint.getSolutions doms cs → modelMember doms cs a

-- ════════════════════════════════════════════════════════════════
-- getSolutions: completeness (no solution is ever missed) — the frontier
-- ════════════════════════════════════════════════════════════════

/-- Completeness (no missing solution): **every** complete, domain-respecting
    assignment that satisfies all the constraints appears in `getSolutions`. This
    is the frontier-hard universal quantifier over the entire domain product: for
    all `a`, if `a` is in the full model set then the solver returns it. Together
    with `spec_solutions_sound` it forces the returned list to be exactly the
    model set — in particular it forbids an incomplete solver (one that prunes too
    aggressively, stops early, or returns only the first solution). Because `a`
    ranges over the frozen `enumerate` product, the law is non-vacuous: for any
    satisfiable CSP there are witnesses `a` that must be present. Over
    `impl.pythonconstraint.getSolutions`, `modelMember`. -/
def spec_solutions_complete (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (cs : List Constraint) (a : Assignment),
    modelMember doms cs a → a ∈ impl.pythonconstraint.getSolutions doms cs

/-- Crown two-sided law: `getSolutions` enumerates **exactly** the full model set.
    For every assignment `a`, `a ∈ getSolutions doms cs ↔ modelMember doms cs a` —
    membership in the returned list coincides with membership in the reference
    model set. This fuses soundness and completeness into one order-independent
    characterization (the solver's own enumeration order is noncanonical, so the
    law is phrased as set membership, not list equality). It is the strongest
    statement of correctness: the solver neither invents nor omits a single
    solution. Over `impl.pythonconstraint.getSolutions`, `modelMember`. -/
def spec_solutions_eq_modelset (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (cs : List Constraint) (a : Assignment),
    (a ∈ impl.pythonconstraint.getSolutions doms cs) ↔ modelMember doms cs a

/-- Strongest crown law — `getSolutions` is a **permutation** of the reference
    model list: `(getSolutions doms cs).Perm (modelList doms cs)`. This is the
    order-independent multiset characterization: the solver returns exactly the
    reference model list up to reordering, so it neither invents, omits, dedups,
    nor duplicates a single solution — even when a domain lists a value more than
    once (`modelList` preserves that multiplicity, which the set-membership
    `spec_solutions_eq_modelset` cannot). Because it is a `Perm` and not a list
    equality, a solver enumerating in any correct order (e.g. python-constraint's
    Degree/MRV order) still satisfies it. Subsumes soundness, completeness, exact
    multiplicity, and the solution count. Over `impl.pythonconstraint.getSolutions`,
    `modelList`. -/
def spec_solutions_perm_model (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (cs : List Constraint),
    (impl.pythonconstraint.getSolutions doms cs).Perm (modelList doms cs)

/-- No duplicate solutions: when every variable's domain is itself duplicate-free
    (`doms.all (·.Nodup)`, the usual case — python-constraint domains are
    conceptually sets), `getSolutions` never returns the same assignment twice.
    Canonical-form pressure — the returned list is a genuine set enumeration (a
    solver that revisits assignments, or double-counts symmetric branches, fails).
    Combined with the model-set law this makes `getSolutions` the duplicate-free
    enumeration of the model set. The domain-`Nodup` guard is necessary and
    faithful: python-constraint does not deduplicate domain values, so a domain
    listing a value twice legitimately yields that solution twice. Over
    `impl.pythonconstraint.getSolutions`. -/
def spec_no_dup_solutions (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (cs : List Constraint),
    doms.all (fun d => d.Nodup) = true →
      (impl.pythonconstraint.getSolutions doms cs).Nodup

-- ════════════════════════════════════════════════════════════════
-- getSolution & solutionCount: cross-API laws
-- ════════════════════════════════════════════════════════════════

/-- `getSolution` existence ⟺ `getSolutions` nonempty: the problem has a single
    solution reported iff it has any solution at all —
    `getSolution doms cs ≠ none ↔ getSolutions doms cs ≠ []`. Cross-API
    consistency: the one-shot solver agrees with the enumerator on satisfiability.
    Over `impl.pythonconstraint.getSolution`, `impl.pythonconstraint.getSolutions`. -/
def spec_getSolution_iff (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (cs : List Constraint),
    (impl.pythonconstraint.getSolution doms cs ≠ none) ↔
      (impl.pythonconstraint.getSolutions doms cs ≠ [])

/-- `getSolution` membership: whenever `getSolution` reports a solution `s`, that
    `s` is one of the full `getSolutions` — the one-shot answer is a genuine
    element of the solution set (not a fabricated assignment). Cross-API law.
    Over `impl.pythonconstraint.getSolution`, `impl.pythonconstraint.getSolutions`. -/
def spec_getSolution_mem (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (cs : List Constraint) (s : Assignment),
    impl.pythonconstraint.getSolution doms cs = some s →
      s ∈ impl.pythonconstraint.getSolutions doms cs

/-- `solutionCount` counts the solutions: `solutionCount doms cs` equals the length
    of `getSolutions doms cs`. Cross-API law pinning the count to the enumerator;
    with the model-set law it becomes the cardinality of the model set. Over
    `impl.pythonconstraint.solutionCount`, `impl.pythonconstraint.getSolutions`. -/
def spec_count_eq_length (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (cs : List Constraint),
    impl.pythonconstraint.solutionCount doms cs =
      (impl.pythonconstraint.getSolutions doms cs).length

/-- Empty solution set on no variables: with no variables (`doms = []`)
    `getSolutions` is empty — faithfully matching python-constraint's
    `Problem.getSolutions`, which returns `[]` when the problem has no variables.
    A boundary law pinning the degenerate case (a solver that returns the single
    empty assignment `[[]]` here fails). Over `impl.pythonconstraint.getSolutions`. -/
def spec_no_variables_empty (impl : RepoImpl) : Prop :=
  ∀ (cs : List Constraint), impl.pythonconstraint.getSolutions [] cs = []

-- ════════════════════════════════════════════════════════════════
-- solution-count, monotonicity, propagation, and unsat-detection laws
-- ════════════════════════════════════════════════════════════════

/-- Unconstrained count is the cartesian-product size: for any non-empty variable
    list and no constraints, `solutionCount doms [] = ∏ dᵢ.length` (`refDomainProduct`).
    Pins the total solution space to the product of the domain sizes, preserving the
    multiplicity of duplicated domain values. Over
    `impl.pythonconstraint.solutionCount`, `refDomainProduct`. -/
def spec_count_no_constraints_product (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)),
    doms ≠ [] →
      impl.pythonconstraint.solutionCount doms [] = refDomainProduct doms

/-- Prepending a constraint is post-filtering: `getSolutions doms (c :: cs)` equals
    `(getSolutions doms cs)` kept to the assignments on which `c` holds (by the
    reference semantics `holdsRef`), in the same order. Pins the incremental effect of
    one constraint to a pure filter of the previous solution list. Over
    `impl.pythonconstraint.getSolutions`, `holdsRef`. -/
def spec_cons_constraint_filter (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (c : Constraint) (cs : List Constraint),
    impl.pythonconstraint.getSolutions doms (c :: cs) =
      (impl.pythonconstraint.getSolutions doms cs).filter (fun a => holdsRef c a)

/-- Constraint-order independence of the solution multiset: if `cs₁` is a permutation
    of `cs₂` then `getSolutions doms cs₁` is a permutation of `getSolutions doms cs₂`.
    Pins the solution set as invariant under reordering the constraint list. Over
    `impl.pythonconstraint.getSolutions`. -/
def spec_constraint_order_perm (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (cs1 cs2 : List Constraint),
    cs1.Perm cs2 →
      (impl.pythonconstraint.getSolutions doms cs1).Perm
        (impl.pythonconstraint.getSolutions doms cs2)

/-- Forward-checking a unary membership restriction preserves the solution multiset:
    for an in-range variable `v`, solving with the extra constraint `inSet [v] allowed`
    yields a permutation of solving after pruning `v`'s domain to the values in
    `allowed` (`refFilterDomainAt`). Pins constraint propagation as solution-set
    preserving. Over `impl.pythonconstraint.getSolutions`, `refFilterDomainAt`. -/
def spec_unary_inset_forward_check (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (v : Nat) (allowed : List Nat) (cs : List Constraint),
    v < doms.length →
      (impl.pythonconstraint.getSolutions doms (.inSet [v] allowed :: cs)).Perm
        (impl.pythonconstraint.getSolutions (refFilterDomainAt doms v allowed) cs)

/-- Returned assignments are canonically keyed: every assignment in `getSolutions` has
    one entry per variable and its keys are exactly `0, 1, …, n-1` in ascending order
    (`refKeys a = List.range doms.length`). Pins the structural well-formedness of the
    solver's output tuples. Over `impl.pythonconstraint.getSolutions`, `refKeys`. -/
def spec_solutions_canonical_keys (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (cs : List Constraint) (a : Assignment),
    a ∈ impl.pythonconstraint.getSolutions doms cs →
      a.length = doms.length ∧ refKeys a = List.range doms.length

/-- Unsatisfiability characterization: `solutionCount doms cs = 0` exactly when no
    assignment is a model (`∀ a, ¬ modelMember doms cs a`). Pins the count-zero case to
    the emptiness of the reference model set, including the no-variable boundary. Over
    `impl.pythonconstraint.solutionCount`, `modelMember`. -/
def spec_count_zero_iff_no_model (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (cs : List Constraint),
    impl.pythonconstraint.solutionCount doms cs = 0 ↔
      ∀ (a : Assignment), ¬ modelMember doms cs a

/-- Distinctness capacity bound: if an `allDifferent` constraint ranges over in-range
    variables whose combined domains hold fewer distinct values than there are
    variables (`(refDedup (refDomainsOfVars doms vars)).length < vars.length`), the CSP
    has no solutions. Pins the capacity limit on simultaneous distinct assignments.
    Over `impl.pythonconstraint.solutionCount`, `refDedup`, `refDomainsOfVars`. -/
def spec_alldiff_capacity_zero (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (vars : List Nat) (cs : List Constraint),
    (∀ v ∈ vars, v < doms.length) →
      (refDedup (refDomainsOfVars doms vars)).length < vars.length →
        impl.pythonconstraint.solutionCount doms (.allDifferent vars :: cs) = 0

/-- Contradictory sum bounds give no solutions: a `minSum vars lo` together with a
    `maxSum vars hi` where `hi < lo` is unsatisfiable, regardless of the domains or
    remaining constraints. Pins the emptiness of an infeasible sum interval. Over
    `impl.pythonconstraint.solutionCount`. -/
def spec_sum_bounds_contradiction_zero (impl : RepoImpl) : Prop :=
  ∀ (doms : List (List Nat)) (vars : List Nat) (lo hi : Nat) (cs : List Constraint),
    hi < lo →
      impl.pythonconstraint.solutionCount doms (.minSum vars lo :: .maxSum vars hi :: cs) = 0
