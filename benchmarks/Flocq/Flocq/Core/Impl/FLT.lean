import Mathlib.Data.Real.Basic
import Flocq.Core.Impl.GenericFmt
import Flocq.Core.Impl.Zaux
import Flocq.Core.Impl.FLX

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Core.Impl.FLT

FLT (floating-point with gradual underflow / subnormals) format foundation
module, translated from the Coq source `src/Core/FLT.v`.

`FLT_exp emin prec e = max(e − prec, emin)` is the FLT exponent function.
It selects the larger of the FLX-style exponent `e − prec` and the
subnormal floor `emin`, thereby encoding gradual underflow.

All Coq real-number types (`R`) and Flocq library operations (`bpow`, `cexp`,
`generic_format`, `round`) are axiomatized as opaque constants; their
algebraic properties are stated only in `Spec/Core.FLT.lean`.

The single computable API exported by this module is `ulp` (unit in the last
place), defined as `bpow (cexp beta fexp x)`.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement only
the function body inside the `!benchmark code` marker.
-/

-- ── Spec helpers (DO NOT MODIFY) ─────────────────────────────────────────────

/-- FLT exponent function: `FLT_exp emin prec e = max(e − prec, emin)`.
    Encodes the FLT floating-point system with minimum exponent `emin` and
    significand precision `prec`.  When `e − prec ≥ emin` the format coincides
    with FLX; when `e − prec < emin` subnormal numbers with exponent `emin`
    are used. -/
def FLT_exp (emin prec : Int) (e : Int) : Int := max (e - prec) emin

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ─────────────────────────────────────────

/-- Signature for `ulp` (unit in the last place): given a radix, an exponent
    function, and a real number, return the size of the unit in the last
    place as a real number. -/
abbrev UlpSig := Radix → (Int → Int) → ℝ → ℝ

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Load-bearing frozen helper (DO NOT MODIFY) ──────────────────────────────
-- `negligibleExp` is referenced by the frozen `Flocq.ulp` below, so it must be
-- frozen too: kept OUTSIDE the agent-editable `global_aux` marker so a codeproof
-- run (which empties `global_aux`) cannot drop it and leave `ulp` referencing an
-- unknown identifier.
/-- Negligible exponent: `some n` (with `n ≤ fexp n`, i.e. a witness that the
    format has a subnormal / constant "negligible" region below `fexp n`) when
    such an `n` exists, otherwise `none`.  Mirrors Coq's `negligible_exp` from
    `src/Core/Ulp.v`, whose LPO-based case split is rendered here with classical
    choice.  For `FLT_exp emin prec` (with `prec > 0`) this yields `some n` with
    `fexp n = emin`; for `FLX_exp` (no underflow bound) it yields `none`. -/
noncomputable def negligibleExp (fexp : Int → Int) : Option Int :=
  open Classical in
  if h : ∃ n : Int, n ≤ fexp n then some (Classical.choose h) else none


noncomputable def Flocq.ulp : Flocq.UlpSig :=
  fun beta fexp x =>
    if x = 0 then
      match negligibleExp fexp with
      | some n => Flocq.bpow beta (fexp n)
      | none   => 0
    else
      Flocq.bpow beta (cexp beta fexp x)
