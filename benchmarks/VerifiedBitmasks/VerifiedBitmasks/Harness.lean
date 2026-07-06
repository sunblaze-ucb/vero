import VerifiedBitmasks.Bundle

/-!
# VerifiedBitmasks.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring, and the `joint_unsat` macro consumed by
`codeproof`-mode `Proof/Joint.lean`.

DO NOT MODIFY this file. This is the benchmark infrastructure.

`RepoImpl` is a `structure` with one field per package (each field typed
as `<Package>Bundle`). Specs always access API functions via
`impl.<pkg>.<fn>`, making the shape uniform across benchmarks.

Per-module proof stubs use direct theorem statements — no macros.
Only `joint_unsat` needs a macro (variadic arity). Specs appear in the
caller's order; no sort / no dedup — anti-cheat is enforced at `!solution`
extraction during evaluation.
-/

-- ── Implementation bundle (one field per package) ──────────────────────

structure RepoImpl where
  verifiedBitmasks : VerifiedBitmasksBundle

-- ── Canonical instance ─────────────────────────────────────────────────
-- Instantiates the package bundle with the reference implementations from
-- `Impl/`. In `proof` mode, `canonical` is the reference implementation
-- (given). In `codeproof` mode, `canonical` points at LLM-filled defs.

def canonical : RepoImpl where
  verifiedBitmasks := {
    -- MachineWords
    bitwiseBit        := VerifiedBitmasks.bitwiseBit
    bitwiseOnes       := VerifiedBitmasks.bitwiseOnes
    bitwiseZeros      := VerifiedBitmasks.bitwiseZeros
    bitwiseMask       := VerifiedBitmasks.bitwiseMask
    bitwiseGetBit     := VerifiedBitmasks.bitwiseGetBit
    bitwiseSetBit     := VerifiedBitmasks.bitwiseSetBit
    bitwiseClearBit   := VerifiedBitmasks.bitwiseClearBit
    bitwiseToggleBit  := VerifiedBitmasks.bitwiseToggleBit
    bitwiseAnd        := VerifiedBitmasks.bitwiseAnd
    bitwiseOr         := VerifiedBitmasks.bitwiseOr
    bitwiseXor        := VerifiedBitmasks.bitwiseXor
    bitwiseNot        := VerifiedBitmasks.bitwiseNot
    bitwiseComp       := VerifiedBitmasks.bitwiseComp
    bitwiseLeftShift  := VerifiedBitmasks.bitwiseLeftShift
    bitwiseRightShift := VerifiedBitmasks.bitwiseRightShift
    bitwiseAdd        := VerifiedBitmasks.bitwiseAdd
    bitwiseSub        := VerifiedBitmasks.bitwiseSub
    bitwiseMul        := VerifiedBitmasks.bitwiseMul
    bitwiseDiv        := VerifiedBitmasks.bitwiseDiv
    bitwiseMod        := VerifiedBitmasks.bitwiseMod
    -- BitmaskIF
    bIF_newZeros      := VerifiedBitmasks.bIF_newZeros
    bIF_newOnes       := VerifiedBitmasks.bIF_newOnes
    bIF_concat        := VerifiedBitmasks.bIF_concat
    bIF_split         := VerifiedBitmasks.bIF_split
    bIF_nbits         := VerifiedBitmasks.bIF_nbits
    bIF_popcnt        := VerifiedBitmasks.bIF_popcnt
    bIF_getBit        := VerifiedBitmasks.bIF_getBit
    bIF_setBit        := VerifiedBitmasks.bIF_setBit
    bIF_clearBit      := VerifiedBitmasks.bIF_clearBit
    bIF_toggleBit     := VerifiedBitmasks.bIF_toggleBit
    bIF_and           := VerifiedBitmasks.bIF_and
    bIF_or            := VerifiedBitmasks.bIF_or
    bIF_xor           := VerifiedBitmasks.bIF_xor
    bIF_not           := VerifiedBitmasks.bIF_not
    -- BitmaskImplIF
    bIIF_newZeros     := bIIF_newZeros
    bIIF_newOnes      := bIIF_newOnes
    bIIF_nbits        := bIIF_nbits
    bIIF_popcnt       := bIIF_popcnt
    bIIF_getBit       := bIIF_getBit
    bIIF_setBit       := bIIF_setBit
    bIIF_clearBit     := bIIF_clearBit
    bIIF_toggleBit    := bIIF_toggleBit
    bIIF_and          := bIIF_and
    bIIF_or           := bIIF_or
    bIIF_xor          := bIIF_xor
    bIIF_not          := bIIF_not
    -- BitmaskFixedChunks
    bFC_newZeros      := bFC_newZeros
    bFC_newOnes       := bFC_newOnes
    bFC_nbits         := bFC_nbits
    bFC_popcnt        := bFC_popcnt
    bFC_getBit        := bFC_getBit
    bFC_setBit        := bFC_setBit
    bFC_clearBit      := bFC_clearBit
    bFC_toggleBit     := bFC_toggleBit
    bFC_and           := bFC_and
    bFC_or            := bFC_or
    bFC_xor           := bFC_xor
    bFC_not           := bFC_not
    -- BitmaskSeq
    bSeq_cNewZeros    := VerifiedBitmasks.bSeq_cNewZeros
    bSeq_cNewOnes     := VerifiedBitmasks.bSeq_cNewOnes
    bSeq_nbits        := VerifiedBitmasks.bSeq_nbits
    bSeq_popcnt       := VerifiedBitmasks.bSeq_popcnt
    bSeq_getBit       := VerifiedBitmasks.bSeq_getBit
    bSeq_setBit       := VerifiedBitmasks.bSeq_setBit
    bSeq_clearBit     := VerifiedBitmasks.bSeq_clearBit
    bSeq_toggleBit    := VerifiedBitmasks.bSeq_toggleBit
    bSeq_eq           := VerifiedBitmasks.bSeq_eq
    bSeq_isZeros      := VerifiedBitmasks.bSeq_isZeros
    bSeq_isOnes       := VerifiedBitmasks.bSeq_isOnes
    bSeq_and          := VerifiedBitmasks.bSeq_and
    bSeq_or           := VerifiedBitmasks.bSeq_or
    bSeq_xor          := VerifiedBitmasks.bSeq_xor
    bSeq_not          := VerifiedBitmasks.bSeq_not
    -- BitmaskArray
    bArr_cNewZeros    := bArr_cNewZeros
    bArr_cNewOnes     := bArr_cNewOnes
    bArr_nbits        := bArr_nbits
    bArr_popcnt       := bArr_popcnt
    bArr_getBit       := bArr_getBit
    bArr_setBit       := bArr_setBit
    bArr_clearBit     := bArr_clearBit
    bArr_toggleBit    := bArr_toggleBit
    bArr_eq           := bArr_eq
    bArr_isZeros      := bArr_isZeros
    bArr_isOnes       := bArr_isOnes
    bArr_and          := bArr_and
    bArr_or           := bArr_or
    bArr_xor          := bArr_xor
    bArr_not          := bArr_not
  }

-- ── joint_unsat macro ──────────────────────────────────────────────────

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
