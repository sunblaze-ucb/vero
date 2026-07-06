import Flocq.Core.Impl.Defs
import Flocq.Calc.Impl.Round

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Calc.Impl.Plus

Floating-point addition kernel, translated from the Coq source
`src/Calc/Plus.v`.

`fplusCore` is the low-level addition engine: given radix `beta`, exponent
function `fexp`, mantissas `m1`/`m2`, exponents `e1`/`e2`, and a target
exponent `e`, it shifts both mantissas to align at `e` and returns their
sum together with the `Location` tracking the rounding error introduced
when shifting m2.

`fplus` is the high-level wrapper: it handles the zero cases, computes
magnitudes via `zdigits`, and either delegates to `fplusCore` (when the
operand magnitudes differ by at least 2) or falls back to exact alignment
addition (mirrors `Operations.Fplus` for close-magnitude operands).

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement only
the function bodies inside the `!benchmark code` markers.
-/

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

/-- Signature for `fplusCore`: given a radix, exponent function, mantissas
    `m1` and `m2`, exponents `e1` and `e2`, and a target exponent `e`,
    compute the aligned sum mantissa and the `Location` recording where the
    true sum sits relative to the returned floating-point number.
    Precondition (not enforced here): `e ≤ e1`. -/
abbrev FplusCoreSig :=
  Radix → (Int → Int) → Int → Int → Int → Int → Int → Int × Location

/-- Signature for `fplus`: add two `FloatNum` values using `fexp` to choose
    the target exponent; return `(mantissa, exponent, location)`. -/
abbrev FplusSig :=
  Radix → (Int → Int) → FloatNum → FloatNum → Int × Int × Location

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=fplusCore
-- !benchmark @end code_aux def=fplusCore

def Flocq.fplusCore : Flocq.FplusCoreSig :=
-- !benchmark @start code def=fplusCore
  fun beta _fexp m1 e1 m2 e2 e =>
    -- k = e - e2: positive means e > e2 (shift m2 right), non-positive means e ≤ e2.
    let k := e - e2
    -- Align m2 to exponent e and compute the location of the rounding error.
    let (m2', l) :=
      if 0 < k then
        -- e > e2: divide m2 by beta^k via truncateAux (tracks location).
        let t := Flocq.truncateAux beta (m2, e2, Location.Exact) k
        (t.1, t.2.2)
      else
        -- e ≤ e2: multiply m2 by beta^(-k) to align upward; result is exact.
        (m2 * beta.val ^ (-k).toNat, Location.Exact)
    -- Align m1 to exponent e (precondition e ≤ e1 ensures non-negative shift).
    let m1' := m1 * beta.val ^ (e1 - e).toNat
    (m1' + m2', l)
-- !benchmark @end code def=fplusCore

-- !benchmark @start code_aux def=fplus
-- !benchmark @end code_aux def=fplus

def Flocq.fplus : Flocq.FplusSig :=
-- !benchmark @start code def=fplus
  fun beta fexp f1 f2 =>
    let m1 := f1.Fnum
    let e1 := f1.Fexp
    let m2 := f2.Fnum
    let e2 := f2.Fexp
    -- Handle zero operands exactly.
    if m1 == 0 then
      (m2, e2, Location.Exact)
    else if m2 == 0 then
      (m1, e1, Location.Exact)
    else
      -- Compute base-beta magnitudes: number-of-digits + exponent.
      let p1 := Flocq.zdigits beta m1 + e1
      let p2 := Flocq.zdigits beta m2 + e2
      -- When magnitudes differ by ≥ 2 we use fplusCore (one operand dominates).
      -- Otherwise fall back to exact alignment addition (mirrors Operations.Fplus).
      if 2 ≤ (p1 - p2).natAbs then
        -- Choose target exponent: min(max(e1,e2), fexp(max(p1,p2) - 1)).
        let e := min (max e1 e2) (fexp (max p1 p2 - 1))
        -- The dominant operand must satisfy e ≤ its exponent; swap if needed.
        let (m, l) :=
          if e1 < e then
            -- e1 < e means e2 ≥ e (the max branch chose e2-side); swap args.
            Flocq.fplusCore beta fexp m2 e2 m1 e1 e
          else
            Flocq.fplusCore beta fexp m1 e1 m2 e2 e
        (m, e, l)
      else
        -- |p1 - p2| < 2: perform exact alignment addition at min(e1, e2).
        -- This mirrors Operations.Fplus (Falign then add mantissas).
        let e := min e1 e2
        let m :=
          m1 * beta.val ^ (e1 - e).toNat + m2 * beta.val ^ (e2 - e).toNat
        (m, e, Location.Exact)
-- !benchmark @end code def=fplus
