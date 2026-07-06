import Flocq.Core.Impl.GenericFmt

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Prop.Impl.Sterbenz

Sterbenz exact subtraction theorem and related exact-addition vocabulary,
translated from the Coq source `src/Prop/Sterbenz.v`.

The Coq file `Sterbenz.v` contains only `Theorem`/`Lemma` items inside a
`Section Fprop_Sterbenz` parameterized by a radix `beta` and an exponent
function `fexp`.  The two key results are:

- `sterbenz`: if `y/2 ≤ x ≤ 2*y` and both `x`, `y` are in generic format,
  then `x − y` is in generic format (the subtraction is exact).
- `generic_format_plus` (restated with same-sign hypothesis): if `x` and `y`
  are in generic format and have the same sign, then `x + y` is in generic
  format.

This module contributes two spec-helper vocabulary definitions:

- `sterbenzAux beta fexp x y` — the exact arithmetic difference `x − y`.
- `genericFormatPlusWeak beta fexp x y` — the Prop asserting that `x + y` is
  in generic format under the weak `|x+y| ≤ min(|x|, |y|)` hypothesis
  (mirroring `generic_format_plus_weak`).

This module has **no computable API functions** — all exported content is
spec-helper vocabulary used by the Spec layer.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Spec helpers (DO NOT MODIFY) ─────────────────────────────────────────────

/-- Auxiliary for the Sterbenz subtraction lemma: the exact arithmetic
    difference `x − y`.  The Sterbenz theorem guarantees that this value lies
    in `genericFormat beta fexp` when `y ≤ x ≤ 2*y` and both `x`, `y` are in
    format.  Mirrors the witness used in Coq's `sterbenz_aux` from
    `src/Prop/Sterbenz.v`. -/
noncomputable def sterbenzAux (beta : Radix) (fexp : Int → Int) (x y : ℝ) : ℝ :=
  x - y

/-- Weak form of the exact-addition condition: `x + y` is in generic format
    given that both `x` and `y` are in format and the absolute value of their
    sum does not exceed either operand in absolute value
    (i.e., `|x+y| ≤ |x|` and `|x+y| ≤ |y|`, the conjunction form of
    `|x+y| ≤ min(|x|, |y|)`).
    Mirrors Coq's `generic_format_plus_weak` from `src/Prop/Sterbenz.v`. -/
def genericFormatPlusWeak (beta : Radix) (fexp : Int → Int) (x y : ℝ) : Prop :=
  genericFormat beta fexp x → genericFormat beta fexp y →
  (|x + y| ≤ |x| ∧ |x + y| ≤ |y|) →
  genericFormat beta fexp (x + y)

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────
-- (This module exposes only the two spec-helper definitions above;
--  no computable API functions are defined here.)

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux
