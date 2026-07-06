import Stack.Bundle

/-!
# Stack.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring all API implementations, and the
`joint_unsat` macro for joint unsatisfiability proofs.

DO NOT MODIFY — benchmark infrastructure.
-/

structure RepoImpl where
  stack : StackBundle

def canonical : RepoImpl where
  stack := {
    isEmpty                    := Stack.isEmpty
    size                       := Stack.size
    isFull                     := Stack.isFull
    peek                       := Stack.peek
    pop                        := Stack.pop
    contains                   := Stack.contains
    fromList                   := Stack.fromList
    balancedParentheses        := balancedParentheses
    infixToPostfix             := infixToPostfix
    infix2Postfix              := infix2Postfix
    infix2Prefix               := infix2Prefix
    dijkstrasTwoStackAlgorithm := dijkstrasTwoStackAlgorithm
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
