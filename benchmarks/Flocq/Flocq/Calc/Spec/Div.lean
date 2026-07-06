import Flocq.Harness
import Flocq.Calc.Impl.Div

/-!
# Flocq.Calc.Spec.Div

Specifications for `fdivCore` and `fdiv`. Each `spec_*` is a property over
an arbitrary `impl : RepoImpl`.

These specs capture the algorithmic correctness of the two APIs at the integer
level, corresponding to the content of the Coq theorems `Fdiv_core_correct`
and `Fdiv_correct` from `src/Calc/Div.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── fdivCore specs ────────────────────────────────────────────────────────────

/-- When `e ≤ e1 - e2`, `fdivCore` shifts the dividend mantissa and returns
    the quotient `(m1 * β^(e1-e2-e)) / m2`.
    Corresponds to the first branch of `Fdiv_core`. -/
def spec_fdivCore_quotient_lo (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    e ≤ e1 - e2 →
    (impl.flocq.fdivCore beta fexp m1 e1 m2 e2 e).1 =
      (m1 * beta.val ^ (e1 - e2 - e).toNat) / m2

/-- When `e > e1 - e2`, `fdivCore` shifts the divisor mantissa and returns
    the quotient `m1 / (m2 * β^(e-(e1-e2)))`.
    Corresponds to the second branch of `Fdiv_core`. -/
def spec_fdivCore_quotient_hi (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    ¬(e ≤ e1 - e2) →
    (impl.flocq.fdivCore beta fexp m1 e1 m2 e2 e).1 =
      m1 / (m2 * beta.val ^ (e - (e1 - e2)).toNat)

/-- When `e ≤ e1 - e2` and the shifted dividend is exactly divisible by `m2`,
    the returned `Location` is `Exact`.
    Corresponds to the `loc_Exact` case of `new_location` when remainder = 0. -/
def spec_fdivCore_exact_lo (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    e ≤ e1 - e2 →
    (m1 * beta.val ^ (e1 - e2 - e).toNat) % m2 = 0 →
    (impl.flocq.fdivCore beta fexp m1 e1 m2 e2 e).2 = Location.Exact

/-- When `e > e1 - e2` and `m1` is exactly divisible by the shifted divisor,
    the returned `Location` is `Exact`. -/
def spec_fdivCore_exact_hi (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    ¬(e ≤ e1 - e2) →
    m1 % (m2 * beta.val ^ (e - (e1 - e2)).toNat) = 0 →
    (impl.flocq.fdivCore beta fexp m1 e1 m2 e2 e).2 = Location.Exact

-- ── fdiv specs ────────────────────────────────────────────────────────────────

/-- `fdiv` returns the target exponent `min (min (fexp e') (fexp (e'+1))) (e1-e2)`,
    where `e' = (zdigits β m1 + e1) − (zdigits β m2 + e2)`.
    Corresponds to the `e` computation in the Coq `Fdiv` definition. -/
def spec_fdiv_exponent (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (x y : FloatNum),
    let e' := (impl.flocq.zdigits beta x.Fnum + x.Fexp) -
              (impl.flocq.zdigits beta y.Fnum + y.Fexp)
    (impl.flocq.fdiv beta fexp x y).2.1 =
      min (min (fexp e') (fexp (e' + 1))) (x.Fexp - y.Fexp)

/-- `fdiv` delegates to `fdivCore` for the mantissa and location: the mantissa
    component of `fdiv x y` equals the quotient from `fdivCore`, and the
    location component equals the location from `fdivCore`.
    Corresponds to the `let '(m, l) := Fdiv_core …` step in Coq `Fdiv`. -/
def spec_fdiv_delegation (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) (x y : FloatNum),
    let e' := (impl.flocq.zdigits beta x.Fnum + x.Fexp) -
              (impl.flocq.zdigits beta y.Fnum + y.Fexp)
    let e := min (min (fexp e') (fexp (e' + 1))) (x.Fexp - y.Fexp)
    let core := impl.flocq.fdivCore beta fexp x.Fnum x.Fexp y.Fnum y.Fexp e
    (impl.flocq.fdiv beta fexp x y).1 = core.1 ∧
    (impl.flocq.fdiv beta fexp x y).2.2 = core.2
