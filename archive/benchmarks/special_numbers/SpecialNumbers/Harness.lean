import SpecialNumbers.Bundle

/-!
# SpecialNumbers.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring, and the `joint_unsat` macro.

DO NOT MODIFY — benchmark infrastructure.
-/

structure RepoImpl where
  specialNumbers : SpecialNumbersBundle

def canonical : RepoImpl where
  specialNumbers := {
    greatest_common_divisor   := SpecialNumbers.greatest_common_divisor
    gcd_by_iterative          := SpecialNumbers.gcd_by_iterative
    armstrong_number          := SpecialNumbers.armstrong_number
    pluperfect_number         := SpecialNumbers.pluperfect_number
    narcissistic_number       := SpecialNumbers.narcissistic_number
    is_automorphic_number     := SpecialNumbers.is_automorphic_number
    bell_numbers              := SpecialNumbers.bell_numbers
    power                     := SpecialNumbers.power
    is_carmichael_number      := SpecialNumbers.is_carmichael_number
    catalan                   := SpecialNumbers.catalan
    hamming                   := SpecialNumbers.hamming
    is_happy_number           := SpecialNumbers.is_happy_number
    int_to_base               := SpecialNumbers.int_to_base
    sum_of_digits             := SpecialNumbers.sum_of_digits
    harshad_numbers_in_base   := SpecialNumbers.harshad_numbers_in_base
    is_harshad_number_in_base := SpecialNumbers.is_harshad_number_in_base
    hexagonal                 := SpecialNumbers.hexagonal
    factorial                 := SpecialNumbers.factorial
    krishnamurthy             := SpecialNumbers.krishnamurthy
    perfect                   := SpecialNumbers.perfect
    polygonal_num             := SpecialNumbers.polygonal_num
    is_pronic                 := SpecialNumbers.is_pronic
    proth                     := SpecialNumbers.proth
    triangular_number         := SpecialNumbers.triangular_number
    ugly_numbers              := SpecialNumbers.ugly_numbers
    factors                   := SpecialNumbers.factors
    abundant                  := SpecialNumbers.abundant
    semi_perfect              := SpecialNumbers.semi_perfect
    weird                     := SpecialNumbers.weird
  }

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
