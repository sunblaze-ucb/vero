import NumberTheory.Bundle

/-!
# NumberTheory.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring, and the `joint_unsat` macro.

DO NOT MODIFY — benchmark infrastructure.
-/

-- ── Implementation bundle (one field per package) ─────────────────────

structure RepoImpl where
  numberTheory : NumberTheoryBundle

-- ── Canonical instance ────────────────────────────────────────────────

def canonical : RepoImpl where
  numberTheory := {
    greatest_common_divisor      := NT.greatest_common_divisor
    gcd_by_iterative             := NT.gcd_by_iterative
    get_factors                  := NT.get_factors
    get_greatest_common_divisor  := NT.get_greatest_common_divisor
    least_common_multiple_slow   := NT.least_common_multiple_slow
    least_common_multiple_fast   := NT.least_common_multiple_fast
    extended_euclidean_algorithm := NT.extended_euclidean_algorithm
    extended_euclid              := NT.extended_euclid
    chinese_remainder_theorem    := NT.chinese_remainder_theorem
    invert_modulo                := NT.invert_modulo
    chinese_remainder_theorem2   := NT.chinese_remainder_theorem2
  }

-- ── joint_unsat macro ─────────────────────────────────────────────────

/-- `joint_unsat spec_A spec_B [spec_C …] by <proof>` generates the
    ∧-conjunction unsat theorem. Variadic; no sort / no dedup — anti-cheat
    is enforced at `!solution` extraction during evaluation. -/
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
