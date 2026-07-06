import Flocq.Core.Impl.Zaux
import Flocq.Core.Impl.Defs

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Calc.Impl.Operations

Exact floating-point arithmetic operations translated from the Coq source
`src/Calc/Operations.v`.

`fmult` is the sole API: it multiplies two `FloatNum` values exactly by
multiplying their mantissas and adding their exponents, corresponding to the
Coq `Fmult` definition.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement only
the function bodies inside the `!benchmark code` markers.
-/

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

/-- Signature for `falign`: align two floats to the smaller exponent and
    return the shifted mantissas with their shared exponent. -/
abbrev FalignSig := Radix → FloatNum → FloatNum → (Int × Int) × Int

/-- Signature for `fopp`: exact floating-point negation. -/
abbrev FoppSig := FloatNum → FloatNum

/-- Signature for `fabs`: exact floating-point absolute value. -/
abbrev FabsSig := FloatNum → FloatNum

/-- Signature for `fmult`: exact multiplication of two floating-point numbers.
    The result mantissa is `f1.Fnum * f2.Fnum` and the result exponent is
    `f1.Fexp + f2.Fexp`. -/
abbrev FmultSig := FloatNum → FloatNum → FloatNum

end Flocq

-- !benchmark @start global_aux
private def powInt (β : Radix) (k : Int) : Int :=
  β.val ^ k.natAbs
-- !benchmark @end global_aux

-- ── falign ───────────────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=falign
-- !benchmark @end code_aux def=falign

def Flocq.falign : Flocq.FalignSig :=
-- !benchmark @start code def=falign
  fun β f1 f2 =>
    if f1.Fexp ≤ f2.Fexp then
      ((f1.Fnum, f2.Fnum * powInt β (f2.Fexp - f1.Fexp)), f1.Fexp)
    else
      ((f1.Fnum * powInt β (f1.Fexp - f2.Fexp), f2.Fnum), f2.Fexp)
-- !benchmark @end code def=falign

-- ── fopp ─────────────────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=fopp
-- !benchmark @end code_aux def=fopp

def Flocq.fopp : Flocq.FoppSig :=
-- !benchmark @start code def=fopp
  fun f => { Fnum := -f.Fnum, Fexp := f.Fexp }
-- !benchmark @end code def=fopp

-- ── fabs ─────────────────────────────────────────────────────────────────────

-- !benchmark @start code_aux def=fabs
-- !benchmark @end code_aux def=fabs

def Flocq.fabs : Flocq.FabsSig :=
-- !benchmark @start code def=fabs
  fun f => { Fnum := Int.ofNat f.Fnum.natAbs, Fexp := f.Fexp }
-- !benchmark @end code def=fabs

-- !benchmark @start code_aux def=fmult
-- !benchmark @end code_aux def=fmult

def Flocq.fmult : Flocq.FmultSig :=
-- !benchmark @start code def=fmult
  fun f1 f2 => { Fnum := f1.Fnum * f2.Fnum, Fexp := f1.Fexp + f2.Fexp }
-- !benchmark @end code def=fmult
