import Ecdsa.Bundle

/-!
# Ecdsa.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring, and the `joint_unsat` macro consumed by
`codeproof`-mode `Proof/Joint.lean`.

DO NOT MODIFY this file. This is the benchmark infrastructure.

Specs always access API functions via `impl.<pkg>.<fn>`.
-/

-- ── Implementation bundle (one field per package) ───────────

structure RepoImpl where
  ecdsa : EcdsaBundle

-- ── Canonical instance ───────────────────────────────────────

def canonical : RepoImpl where
  ecdsa := {
    inverseMod    := Ecdsa.inverseMod
    isOddPrime    := Ecdsa.isOddPrime
    jacobi        := Ecdsa.jacobi
    sqrtModPrime  := Ecdsa.sqrtModPrime
    containsPoint := Ecdsa.containsPoint
    negPoint      := Ecdsa.negPoint
    pointDouble   := Ecdsa.pointDouble
    pointAdd      := Ecdsa.pointAdd
    scalarMult    := Ecdsa.scalarMult
  }

-- ── joint_unsat macro ────────────────────────────────────────

/--
`joint_unsat spec_A spec_B [spec_C …] by <proof>` generates
```
theorem joint_unsat.spec_A.spec_B.… :
    ¬ ∃ impl : RepoImpl, spec_A impl ∧ spec_B impl ∧ … := by <proof>
```

Specs appear in the caller's order. No sorting, no deduplication —
anti-cheat for joint-unsat claims is enforced at evaluation by
extracting the spec list from the companion `!solution` marker
(rejecting duplicates there) and rerendering this macro from the
extracted list.
-/
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
