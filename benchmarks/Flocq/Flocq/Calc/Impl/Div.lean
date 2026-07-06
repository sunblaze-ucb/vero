import Flocq.Core.Impl.Defs
import Flocq.Core.Impl.Digits
import Flocq.Calc.Impl.Bracket

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Calc.Impl.Div

Floating-point division kernel, translated from the Coq source `src/Calc/Div.v`.

`fdivCore` is the low-level division engine: given radix `beta`, exponent
function `fexp`, mantissas `m1`/`m2`, exponents `e1`/`e2`, and a target
exponent `e`, it shifts one mantissa to align the division at `e`, performs
integer (Euclidean-style) division, and returns the quotient mantissa together
with the `Location` that records where the true quotient sits relative to the
returned float.

`fdiv` is the high-level wrapper: it computes the optimal target exponent via
`fexp`, delegates to `fdivCore`, and returns the full triple
`(mantissa, exponent, location)`.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement only
the function bodies inside the `!benchmark code` markers.
-/

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

/-- Signature for `fdivCore`: given a radix, exponent function, mantissas `m1`
    and `m2`, exponents `e1` and `e2`, and a target exponent `e`, compute the
    quotient mantissa and the `Location` of the true quotient relative to the
    returned floating-point number. -/
abbrev FdivCoreSig :=
  Radix → (Int → Int) → Int → Int → Int → Int → Int → Int × Location

/-- Signature for `fdiv`: divide two `FloatNum` values using `fexp` to choose
    the target exponent; return `(mantissa, exponent, location)`. -/
abbrev FdivSig :=
  Radix → (Int → Int) → FloatNum → FloatNum → Int × Int × Location

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=fdivCore
-- !benchmark @end code_aux def=fdivCore

def Flocq.fdivCore : Flocq.FdivCoreSig :=
-- !benchmark @start code def=fdivCore
  fun beta _fexp m1 e1 m2 e2 e =>
    -- Shift one mantissa so the division aligns at the target exponent e.
    -- Branch on whether e ≤ e1 - e2 (shift dividend) or e > e1 - e2 (shift divisor).
    let (m1', m2') :=
      if e ≤ e1 - e2 then
        (m1 * beta.val ^ (e1 - e2 - e).toNat, m2)
      else
        (m1, m2 * beta.val ^ (e - (e1 - e2)).toNat)
    -- Euclidean-style integer division: for positive m1', m2', Int `/` and `%`
    -- agree with Coq's Z.div_eucl.
    let q := m1' / m2'
    let r := m1' % m2'
    -- Compute location: newLocation m2' r loc_Exact encodes where the true
    -- quotient sits relative to q (Exact when r = 0, Inexact otherwise).
    (q, Flocq.newLocation m2' r Location.Exact)
-- !benchmark @end code def=fdivCore

-- !benchmark @start code_aux def=fdiv
-- !benchmark @end code_aux def=fdiv

def Flocq.fdiv : Flocq.FdivSig :=
-- !benchmark @start code def=fdiv
  fun beta fexp x y =>
    let m1 := x.Fnum
    let e1 := x.Fexp
    let m2 := y.Fnum
    let e2 := y.Fexp
    -- e' is the magnitude estimate: (digits(m1) + e1) - (digits(m2) + e2)
    let e' := (Flocq.zdigits beta m1 + e1) - (Flocq.zdigits beta m2 + e2)
    -- Choose the smallest valid target exponent, bounded by e1 - e2 to keep
    -- the shift non-negative.
    let e := min (min (fexp e') (fexp (e' + 1))) (e1 - e2)
    let (m, l) := Flocq.fdivCore beta fexp m1 e1 m2 e2 e
    (m, e, l)
-- !benchmark @end code def=fdiv
