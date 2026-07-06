import SuffixTree.Bundle

/-!
# SuffixTree.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring, and the `joint_unsat` macro consumed by
`codeproof`-mode `Proof/Joint.lean`.

DO NOT MODIFY this file. This is the benchmark infrastructure.

`RepoImpl` is uniformly a `structure` with one field per package (each
field typed as `<Package>Bundle`). Single-package benchmarks (this
one) have exactly one field. Multi-package benchmarks add one field
per sibling package. Specs always access API functions via
`impl.<pkg>.<fn>`, making the shape the same across cases.

Per-module proof stubs use direct theorem statements — no macros.
Only `joint_unsat` needs a macro (variadic arity). Specs appear in
the caller's order; no sort / no dedup — anti-cheat is enforced at
`!solution` extraction during evaluation.
-/

-- ── Implementation bundle (one field per package) ────────────────────

structure RepoImpl where
  suffixTree : SuffixTreeBundle

-- ── Canonical instance ───────────────────────────────────────────────
-- Instantiates the bundle with the reference implementations from
-- `Impl/SuffixTree.lean`. In `proof` mode, `canonical` is the given
-- reference. In `codeproof` mode, `canonical` points at LLM-filled
-- `SuffixTree.*` defs.

def canonical : RepoImpl where
  suffixTree := {
    mk              := SuffixTree.mk
    buildSuffixTree := SuffixTree.buildSuffixTree
    addSuffix       := SuffixTree.addSuffix
    search          := SuffixTree.search
  }

-- ── joint_unsat macro ────────────────────────────────────────────────

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
