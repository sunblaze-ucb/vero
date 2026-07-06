import Flocq.Bundle

/-!
# Flocq.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring, and the `joint_unsat` macro consumed by
`codeproof`-mode `Proof/Joint.lean`.

DO NOT MODIFY — benchmark infrastructure.

`RepoImpl` has a single field `flocq : FlocqBundle` (single-package benchmark).
Specs always access API functions via `impl.flocq.<fn>`, making the shape
consistent across single- and multi-package benchmarks.
-/

-- ── Implementation bundle (one field: the flocq package) ─────────────────────

structure RepoImpl where
  flocq : FlocqBundle

-- ── Canonical instance ────────────────────────────────────────────────────────
-- Instantiates the bundle with the reference implementations from the Impl/
-- files.  In `proof` mode this is the given reference; in `codeproof` mode it
-- points at LLM-filled `Flocq.*` defs.

noncomputable def canonical : RepoImpl where
  flocq := {
    zfastPowPos      := Flocq.zfastPowPos
    zposDivEuclAux1  := Flocq.zposDivEuclAux1
    zposDivEuclAux   := Flocq.zposDivEuclAux
    zfastDivEucl     := Flocq.zfastDivEucl
    iterNat           := Flocq.iterNat
    rcompare          := Flocq.rcompare
    rleBool           := Flocq.rleBool
    rltBool           := Flocq.rltBool
    reqBool           := Flocq.reqBool
    ztrunc            := Flocq.ztrunc
    zaway             := Flocq.zaway
    bpow              := Flocq.bpow
    condRopp          := Flocq.condRopp
    znearest          := Flocq.znearest
    round             := Flocq.round
    ulp               := Flocq.ulp
    succ              := Flocq.succ
    pred              := Flocq.pred
    digits2Pnat       := Flocq.digits2Pnat
    zsumDigit         := Flocq.zsumDigit
    zscale            := Flocq.zscale
    zslice            := Flocq.zslice
    zdigitsAux        := Flocq.zdigitsAux
    zdigits           := Flocq.zdigits
    newLocationEven   := Flocq.newLocationEven
    newLocationOdd    := Flocq.newLocationOdd
    newLocation       := Flocq.newLocation
    falign            := Flocq.falign
    fopp              := Flocq.fopp
    fabs              := Flocq.fabs
    fmult             := Flocq.fmult
    fdivCore          := Flocq.fdivCore
    fdiv              := Flocq.fdiv
    fplusCore         := Flocq.fplusCore
    fplus             := Flocq.fplus
    condIncr          := Flocq.condIncr
    roundSignDN       := Flocq.roundSignDN
    roundUP           := Flocq.roundUP
    roundSignUP       := Flocq.roundSignUP
    roundZR           := Flocq.roundZR
    roundN            := Flocq.roundN
    truncateAux       := Flocq.truncateAux
    truncate          := Flocq.truncate
    truncateFIX       := Flocq.truncateFIX
    fsqrtCore         := Flocq.fsqrtCore
    fsqrt             := Flocq.fsqrt
    b2R               := Flocq.b2R
    isFinite          := Flocq.isFinite
    isNaN             := Flocq.isNaN
    roundMode         := Flocq.roundMode
    b2FF              := Flocq.b2FF
    ff2B              := Flocq.ff2B
    binaryNormalize   := Flocq.binaryNormalize
    babs              := Flocq.babs
    bcompare          := Flocq.bcompare
    bdiv              := Flocq.bdiv
    bfma              := Flocq.bfma
    bfrexp            := Flocq.bfrexp
    bldexp            := Flocq.bldexp
    bmaxFloat         := Flocq.bmaxFloat
    bminus            := Flocq.bminus
    bmult             := Flocq.bmult
    bnearbyint        := Flocq.bnearbyint
    bone              := Flocq.bone
    bopp              := Flocq.bopp
    bplus             := Flocq.bplus
    bpred             := Flocq.bpred
    bsqrt             := Flocq.bsqrt
    bsucc             := Flocq.bsucc
    btrunc            := Flocq.btrunc
    bulp              := Flocq.bulp
    validBinary       := Flocq.validBinary
    binopNanPl32      := Flocq.binopNanPl32
    binopNanPl64      := Flocq.binopNanPl64
    unopNanPl32       := Flocq.unopNanPl32
    unopNanPl64       := Flocq.unopNanPl64
    ternopNanPl32     := Flocq.ternopNanPl32
    ternopNanPl64     := Flocq.ternopNanPl64
    splitBits         := Flocq.splitBits
    splitBitsOfBinaryFloat := Flocq.splitBitsOfBinaryFloat
    binaryFloatOfBitsAux := Flocq.binaryFloatOfBitsAux
    bitsOfBinaryFloat := Flocq.bitsOfBinaryFloat
    binaryFloatOfBits := Flocq.binaryFloatOfBits
    b32OfBits         := Flocq.b32OfBits
    b64OfBits         := Flocq.b64OfBits
    bitsOfB32         := Flocq.bitsOfB32
    bitsOfB64         := Flocq.bitsOfB64
    b32Plus           := Flocq.b32Plus
    b32Minus          := Flocq.b32Minus
    b32Mult           := Flocq.b32Mult
    b32Div            := Flocq.b32Div
    b32Sqrt           := Flocq.b32Sqrt
    b32Fma            := Flocq.b32Fma
    b64Plus           := Flocq.b64Plus
    b64Minus          := Flocq.b64Minus
    b64Mult           := Flocq.b64Mult
    b64Div            := Flocq.b64Div
    b64Sqrt           := Flocq.b64Sqrt
    b64Fma            := Flocq.b64Fma
    b2Prim            := Flocq.b2Prim
    prim2B            := Flocq.prim2B
    pffFopp           := Flocq.pffFopp
    pffFabs           := Flocq.pffFabs
    pffFplus          := Flocq.pffFplus
    pffFmult          := Flocq.pffFmult
    pffMZlistAux      := Flocq.pffMZlistAux
    pffMZlist         := Flocq.pffMZlist
    pffMProd          := Flocq.pffMProd
  }

-- ── joint_unsat macro ─────────────────────────────────────────────────────────

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
