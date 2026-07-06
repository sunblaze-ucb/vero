import Flocq.Harness
import Flocq.Calc.Impl.Plus

/-!
# Flocq.Calc.Spec.Plus

Specifications for `fplusCore` and `fplus`. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`.

These specs capture the algorithmic correctness of the two APIs at the
integer level, corresponding to the content of the Coq theorems
`Fplus_core_correct` and `Fplus_correct` from `src/Calc/Plus.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── fplusCore specs ────────────────────────────────────────────────────────────

/-- When `e ≤ e2` (the shift is non-positive), `fplusCore` aligns both
    mantissas by multiplication and returns their exact sum.
    Corresponds to the else-branch of `Fplus_core` where
    `m2' = m2 * β^(e2-e)` and `l = loc_Exact`. -/
def spec_fplusCore_mantissa_lo (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    e ≤ e2 →
    (impl.flocq.fplusCore beta fexp m1 e1 m2 e2 e).1 =
      m1 * beta.val ^ (e1 - e).toNat + m2 * beta.val ^ (e2 - e).toNat

/-- When `e ≤ e2`, `fplusCore` returns `Location.Exact` (no rounding error).
    Corresponds to the `loc_Exact` in the else-branch of `Fplus_core`. -/
def spec_fplusCore_location_exact_lo (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    e ≤ e2 →
    (impl.flocq.fplusCore beta fexp m1 e1 m2 e2 e).2 = Location.Exact

/-- When `e > e2`, `fplusCore` divides `m2` by `β^(e-e2)` to align it at `e`.
    The returned mantissa is `m1 * β^(e1-e) + m2 / β^(e-e2)`.
    Corresponds to the `truncate_aux` branch of `Fplus_core`. -/
def spec_fplusCore_mantissa_hi (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    e > e2 →
    (impl.flocq.fplusCore beta fexp m1 e1 m2 e2 e).1 =
      m1 * beta.val ^ (e1 - e).toNat + m2 / beta.val ^ (e - e2).toNat

/-- When `e > e2` and `β^(e-e2)` divides `m2` exactly, `fplusCore` returns
    `Location.Exact` (truncation introduced no rounding error).
    Corresponds to the `new_location p 0 loc_Exact = loc_Exact` case. -/
def spec_fplusCore_location_exact_hi (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    e > e2 →
    m2 % beta.val ^ (e - e2).toNat = 0 →
    (impl.flocq.fplusCore beta fexp m1 e1 m2 e2 e).2 = Location.Exact

-- ── fplus specs ───────────────────────────────────────────────────────────────

/-- When the left mantissa is zero, `fplus` returns the right operand exactly.
    Corresponds to the `Zeq_bool m1 0` branch of `Fplus`. -/
def spec_fplus_zero_left (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (f1 f2 : FloatNum),
    f1.Fnum = 0 →
    impl.flocq.fplus beta fexp f1 f2 = (f2.Fnum, f2.Fexp, Location.Exact)

/-- When the right mantissa is zero (and the left is nonzero), `fplus` returns
    the left operand exactly.
    Corresponds to the `Zeq_bool m2 0` branch of `Fplus`. -/
def spec_fplus_zero_right (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (f1 f2 : FloatNum),
    f1.Fnum ≠ 0 → f2.Fnum = 0 →
    impl.flocq.fplus beta fexp f1 f2 = (f1.Fnum, f1.Fexp, Location.Exact)

/-- When both mantissas are nonzero and `|p1 - p2| ≥ 2`, the exponent
    component of `fplus` is `min (max e1 e2) (fexp (max p1 p2 - 1))`,
    where `p1 = zdigits β m1 + e1` and `p2 = zdigits β m2 + e2`.
    Corresponds to the target-exponent computation in `Fplus`. -/
def spec_fplus_exponent_large_gap (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (f1 f2 : FloatNum),
    f1.Fnum ≠ 0 → f2.Fnum ≠ 0 →
    let p1 := impl.flocq.zdigits beta f1.Fnum + f1.Fexp
    let p2 := impl.flocq.zdigits beta f2.Fnum + f2.Fexp
    2 ≤ (p1 - p2).natAbs →
    (impl.flocq.fplus beta fexp f1 f2).2.1 =
      min (max f1.Fexp f2.Fexp) (fexp (max p1 p2 - 1))

/-- When both mantissas are nonzero and `|p1 - p2| < 2`, `fplus` performs
    exact alignment addition at exponent `min(e1, e2)`: the mantissa is
    `m1 * β^(e1-e) + m2 * β^(e2-e)`, the exponent is `min(e1, e2)`, and
    the location is `Exact`.
    Corresponds to the `Operations.Fplus` fallback in `Fplus`. -/
def spec_fplus_exact_close (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (f1 f2 : FloatNum),
    f1.Fnum ≠ 0 → f2.Fnum ≠ 0 →
    let p1 := impl.flocq.zdigits beta f1.Fnum + f1.Fexp
    let p2 := impl.flocq.zdigits beta f2.Fnum + f2.Fexp
    (p1 - p2).natAbs < 2 →
    let e := min f1.Fexp f2.Fexp
    impl.flocq.fplus beta fexp f1 f2 =
      (f1.Fnum * beta.val ^ (f1.Fexp - e).toNat +
       f2.Fnum * beta.val ^ (f2.Fexp - e).toNat,
       e, Location.Exact)
