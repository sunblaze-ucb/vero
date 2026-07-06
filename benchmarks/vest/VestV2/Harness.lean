import VestV2.Bundle

/-!
# VestV2.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring, and the `joint_unsat` macro.

`RepoImpl` is the live candidate surface for this benchmark. Support
modules imported elsewhere in the project are fixed curator context
unless they are wired through `Bundle` and constrained by obligation
specs in the manifest.

DO NOT MODIFY — benchmark infrastructure.
-/

-- ── Implementation bundle (one field per package) ───────────

structure RepoImpl where
  vest : VestV2Bundle

-- ── Canonical instance ───────────────────────────────────────

def canonical : RepoImpl where
  vest := {
    fromParseError     := VestV2.fromParseError
    fromSerializeError := VestV2.fromSerializeError
    setRange           := VestV2.setRange
    compareSlice       := VestV2.compareSlice
    initVecU8          := VestV2.initVecU8
    variableParse      := VestV2.variableParse
    variableSerialize  := VestV2.variableSerialize
    fixedParse         := VestV2.fixedParse
    fixedSerialize     := VestV2.fixedSerialize
    tailParse          := VestV2.tailParse
    tailSerialize      := VestV2.tailSerialize
    endParse           := VestV2.endParse
    endSerialize       := VestV2.endSerialize
    failParse          := VestV2.failParse
    failSerialize      := VestV2.failSerialize
    successParse       := VestV2.successParse
    successSerialize   := VestV2.successSerialize
    leb128Parse        := VestV2.leb128Parse
    cloneU8            := VestV2.cloneU8
    cloneU16Le         := VestV2.cloneU16Le
    cloneU32Le         := VestV2.cloneU32Le
    cloneU64Le         := VestV2.cloneU64Le
    cloneTail          := VestV2.cloneTail
    cloneVariable      := VestV2.cloneVariable
    cloneFixed         := VestV2.cloneFixed
    tagParse           := VestV2.tagParse
    tagSerialize       := VestV2.tagSerialize
    btcVarintParse     := VestV2.btcVarintParse
    btcVarintSerialize := VestV2.btcVarintSerialize
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
