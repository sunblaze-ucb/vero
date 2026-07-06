import Flocq.Harness
import Flocq.Calc.Impl.Operations

/-!
# Flocq.Calc.Spec.Operations

Specifications for exact floating-point operations.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

These specs correspond to the structural content of the Coq theorem `F2R_mult`
from `src/Calc/Operations.v`: exact multiplication multiplies mantissas and
adds exponents.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- If the first exponent is no larger, `falign` keeps it as the shared
    exponent. -/
def spec_falign_exp_le (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (f1 f2 : FloatNum),
    f1.Fexp ≤ f2.Fexp →
    (impl.flocq.falign β f1 f2).2 = f1.Fexp

/-- If the second exponent is smaller, `falign` keeps it as the shared
    exponent. -/
def spec_falign_exp_gt (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (f1 f2 : FloatNum),
    ¬ f1.Fexp ≤ f2.Fexp →
    (impl.flocq.falign β f1 f2).2 = f2.Fexp

/-- In the `f1.Fexp ≤ f2.Fexp` branch, `falign` leaves the first mantissa
    unchanged. -/
def spec_falign_left_mantissa_le (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (f1 f2 : FloatNum),
    f1.Fexp ≤ f2.Fexp →
    (impl.flocq.falign β f1 f2).1.1 = f1.Fnum

/-- In the `f1.Fexp ≤ f2.Fexp` branch, `falign` scales the second mantissa by
    the exponent difference. -/
def spec_falign_right_mantissa_le (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (f1 f2 : FloatNum),
    f1.Fexp ≤ f2.Fexp →
    (impl.flocq.falign β f1 f2).1.2 =
      f2.Fnum * β.val ^ (f2.Fexp - f1.Fexp).natAbs

/-- `fopp` negates the mantissa. -/
def spec_fopp_num (impl : RepoImpl) : Prop :=
  ∀ (f : FloatNum), (impl.flocq.fopp f).Fnum = -f.Fnum

/-- `fopp` preserves the exponent. -/
def spec_fopp_exp (impl : RepoImpl) : Prop :=
  ∀ (f : FloatNum), (impl.flocq.fopp f).Fexp = f.Fexp

/-- `fabs` returns the absolute value of the mantissa. -/
def spec_fabs_num (impl : RepoImpl) : Prop :=
  ∀ (f : FloatNum), (impl.flocq.fabs f).Fnum = Int.ofNat f.Fnum.natAbs

/-- `fabs` preserves the exponent. -/
def spec_fabs_exp (impl : RepoImpl) : Prop :=
  ∀ (f : FloatNum), (impl.flocq.fabs f).Fexp = f.Fexp

/-- `fmult` yields a result whose mantissa is the product of the two input
    mantissas. This is the mantissa half of the Coq `Fmult` definition. -/
def spec_fmult_mantissa (impl : RepoImpl) : Prop :=
  ∀ (f1 f2 : FloatNum),
    (impl.flocq.fmult f1 f2).Fnum = f1.Fnum * f2.Fnum

/-- `fmult` yields a result whose exponent is the sum of the two input
    exponents. This is the exponent half of the Coq `Fmult` definition. -/
def spec_fmult_exponent (impl : RepoImpl) : Prop :=
  ∀ (f1 f2 : FloatNum),
    (impl.flocq.fmult f1 f2).Fexp = f1.Fexp + f2.Fexp
