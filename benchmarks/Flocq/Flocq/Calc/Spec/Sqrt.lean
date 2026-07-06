import Flocq.Harness
import Flocq.Calc.Impl.Sqrt

/-!
# Flocq.Calc.Spec.Sqrt

Specifications for `fsqrtCore` and `fsqrt`. Each `spec_*` is a property over
an arbitrary `impl : RepoImpl`.

These specs capture the algorithmic correctness of the two APIs at the integer
level, corresponding to the content of the Coq theorem `Fsqrt_core_correct`
and `Fsqrt_correct` from `src/Calc/Sqrt.v`. The real-valued inbetween_float
correctness statements are abstracted to their integer-level components: the
mantissa is the integer square root of the shifted mantissa, and the location
encodes the position of the remainder relative to the root.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── fsqrtCore specs ───────────────────────────────────────────────────────────

/-- The mantissa returned by `fsqrtCore` is the integer square root of the
    shifted mantissa `m1 * β^(e1 − 2e)`.
    Corresponds to the `q` computed via `Z.sqrtrem` in Coq's `Fsqrt_core`. -/
def spec_fsqrtCore_mantissa (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (m1 e1 e : Int),
    0 < m1 → 2 * e ≤ e1 →
    let m1' := m1 * beta.val ^ (e1 - 2 * e).toNat
    (impl.flocq.fsqrtCore beta m1 e1 e).1 * (impl.flocq.fsqrtCore beta m1 e1 e).1 ≤ m1' ∧
    m1' < ((impl.flocq.fsqrtCore beta m1 e1 e).1 + 1) *
          ((impl.flocq.fsqrtCore beta m1 e1 e).1 + 1)

/-- When the shifted mantissa `m1 * β^(e1−2e)` is a perfect square (remainder = 0),
    `fsqrtCore` returns `Location.Exact`.
    Corresponds to the `Zeq_bool r 0 = true` branch of `Fsqrt_core`. -/
def spec_fsqrtCore_exact (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (m1 e1 e : Int),
    0 < m1 → 2 * e ≤ e1 →
    let m1' := m1 * beta.val ^ (e1 - 2 * e).toNat
    let q := (impl.flocq.fsqrtCore beta m1 e1 e).1
    m1' = q * q →
    (impl.flocq.fsqrtCore beta m1 e1 e).2 = Location.Exact

/-- When the remainder is nonzero and at most the root, `fsqrtCore` returns
    `Location.Inexact Ordering.lt` (true root is below the midpoint of the
    bracketing interval).
    Corresponds to the `Zle_bool r q = true` branch of `Fsqrt_core`. -/
def spec_fsqrtCore_inexact_lo (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (m1 e1 e : Int),
    0 < m1 → 2 * e ≤ e1 →
    let m1' := m1 * beta.val ^ (e1 - 2 * e).toNat
    let q := (impl.flocq.fsqrtCore beta m1 e1 e).1
    let r := m1' - q * q
    r ≠ 0 → r ≤ q →
    (impl.flocq.fsqrtCore beta m1 e1 e).2 = Location.Inexact Ordering.lt

/-- When the remainder is nonzero and strictly greater than the root,
    `fsqrtCore` returns `Location.Inexact Ordering.gt` (true root is above
    the midpoint of the bracketing interval).
    Corresponds to the `Zle_bool r q = false` branch of `Fsqrt_core`. -/
def spec_fsqrtCore_inexact_hi (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (m1 e1 e : Int),
    0 < m1 → 2 * e ≤ e1 →
    let m1' := m1 * beta.val ^ (e1 - 2 * e).toNat
    let q := (impl.flocq.fsqrtCore beta m1 e1 e).1
    let r := m1' - q * q
    r ≠ 0 → r > q →
    (impl.flocq.fsqrtCore beta m1 e1 e).2 = Location.Inexact Ordering.gt

-- ── fsqrt specs ───────────────────────────────────────────────────────────────

/-- `fsqrt` returns the target exponent `min (fexp (zdiv2 e')) (zdiv2 e1)`,
    where `e' = zdigits β m1 + e1 + 1` and `zdiv2` is floor division by 2
    (Coq's `Z.div2`).
    Corresponds to the `e` computation in Coq's `Fsqrt`. -/
def spec_fsqrt_exponent (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (x : FloatNum),
    let e' := impl.flocq.zdigits beta x.Fnum + x.Fexp + 1
    (impl.flocq.fsqrt beta fexp x).2.1 =
      min (fexp (Flocq.zdiv2 e')) (Flocq.zdiv2 x.Fexp)

/-- `fsqrt` delegates to `fsqrtCore` for the mantissa and location: the
    mantissa component of `fsqrt x` equals the mantissa from `fsqrtCore`, and
    the location component equals the location from `fsqrtCore`.
    Corresponds to the `let '(m, l) := Fsqrt_core …` step in Coq's `Fsqrt`. -/
def spec_fsqrt_delegation (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (x : FloatNum),
    let e' := impl.flocq.zdigits beta x.Fnum + x.Fexp + 1
    let e := min (fexp (Flocq.zdiv2 e')) (Flocq.zdiv2 x.Fexp)
    let core := impl.flocq.fsqrtCore beta x.Fnum x.Fexp e
    (impl.flocq.fsqrt beta fexp x).1 = core.1 ∧
    (impl.flocq.fsqrt beta fexp x).2.2 = core.2
