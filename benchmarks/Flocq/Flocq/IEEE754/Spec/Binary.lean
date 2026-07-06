import Flocq.Harness
import Flocq.IEEE754.Impl.Binary

open Flocq

/-!
# Flocq.IEEE754.Spec.Binary

Specifications for the IEEE 754 binary floating-point operations defined in
`Impl/IEEE754.Binary.lean`, corresponding to key theorems from
`src/IEEE754/Binary.v`.

The specs cover correctness of all arithmetic operations on finite inputs:
`bplus`, `bminus`, `bmult`, `bdiv`, `bsqrt`, `bfma`, `bldexp`, `bfrexp`,
`bcompare`, `bnearbyint`, `btrunc`, `bone`, `bsucc`, `bpred`, `bulp`.

Spec helpers (`b2R`, `rndFLT`, `isFinite`, `isNaN`, `Rcompare`, `roundMode`,
`Ztrunc`, `Flocq.bpow`, `Flocq.succ`, `Flocq.pred`, `Flocq.ulp`, `FLT_exp`)
are imported from `Impl/IEEE754.Binary.lean` and the transitively imported
modules. `BplusSig` et al. have `mode : RoundingMode` before the `nanH`
handler — specs follow that parameter order.

All specs access benchmarked API functions via `impl.flocq.*` through
`RepoImpl`. Direct uses of `Flocq.bpow`, `Flocq.succ`, etc. refer to the
axiomatized reference functions, not the benchmarked slot.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `b2R` exposes the shared real-value projection helper. -/
def spec_b2R_def (impl : RepoImpl) : Prop :=
  (∀ (prec emax : Int) (s : Bool),
    impl.flocq.b2R prec emax (BinaryFloat.zero s) = 0) ∧
  (∀ (prec emax : Int) (s : Bool),
    impl.flocq.b2R prec emax (BinaryFloat.inf s) = 0) ∧
  (∀ (prec emax : Int) (s : Bool) (payload : Nat),
    impl.flocq.b2R prec emax (BinaryFloat.nan s payload) = 0) ∧
  (∀ (prec emax : Int) (s : Bool) (m : Nat) (e : Int),
    impl.flocq.b2R prec emax (BinaryFloat.finite s m e) =
      (if s then -1 else 1 : ℝ) * (m : ℝ) * Flocq.bpow radix2 e)

/-- `isFinite` exposes the shared finite-value predicate helper. -/
def spec_isFinite_def (impl : RepoImpl) : Prop :=
  (∀ (prec emax : Int) (s : Bool),
    impl.flocq.isFinite prec emax (BinaryFloat.zero s) = true) ∧
  (∀ (prec emax : Int) (s : Bool),
    impl.flocq.isFinite prec emax (BinaryFloat.inf s) = false) ∧
  (∀ (prec emax : Int) (s : Bool) (payload : Nat),
    impl.flocq.isFinite prec emax (BinaryFloat.nan s payload) = false) ∧
  (∀ (prec emax : Int) (s : Bool) (m : Nat) (e : Int),
    impl.flocq.isFinite prec emax (BinaryFloat.finite s m e) = true)

/-- `isNaN` exposes the shared NaN predicate helper. -/
def spec_isNaN_def (impl : RepoImpl) : Prop :=
  (∀ (prec emax : Int) (s : Bool),
    impl.flocq.isNaN prec emax (BinaryFloat.zero s) = false) ∧
  (∀ (prec emax : Int) (s : Bool),
    impl.flocq.isNaN prec emax (BinaryFloat.inf s) = false) ∧
  (∀ (prec emax : Int) (s : Bool) (payload : Nat),
    impl.flocq.isNaN prec emax (BinaryFloat.nan s payload) = true) ∧
  (∀ (prec emax : Int) (s : Bool) (m : Nat) (e : Int),
    impl.flocq.isNaN prec emax (BinaryFloat.finite s m e) = false)

/-- `roundMode` exposes the shared IEEE rounding-mode interpretation helper. -/
def spec_roundMode_def (impl : RepoImpl) : Prop :=
  (∀ (x : ℝ), impl.flocq.roundMode RoundingMode.DN x = Zfloor x) ∧
  (∀ (x : ℝ), impl.flocq.roundMode RoundingMode.UP x = Zceil x) ∧
  (∀ (x : ℝ), impl.flocq.roundMode RoundingMode.ZR x = Ztrunc x) ∧
  (∀ (x : ℝ), impl.flocq.roundMode RoundingMode.NE x = Znearest (fun _ => false) x) ∧
  (∀ (x : ℝ), impl.flocq.roundMode RoundingMode.NA x = Znearest (fun _ => true) x)

/-- `b2FF` is the identity conversion in the benchmark representation. -/
def spec_b2FF_identity (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) (x : BinaryFloat prec emax),
    impl.flocq.b2FF prec emax x = x

/-- `ff2B` is the identity conversion in the benchmark representation. -/
def spec_ff2B_identity (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) (x : BinaryFloat prec emax),
    impl.flocq.ff2B prec emax x = x

/-- `binaryNormalize` agrees with the reference normalization helper. -/
def spec_binaryNormalize_def (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) (mode : RoundingMode) (m e : Int) (szero : Bool),
    impl.flocq.binaryNormalize prec emax mode m e szero =
      Flocq.binaryNormalize prec emax mode m e szero

/-- `babs` delegates NaN inputs to the supplied NaN handler. -/
def spec_babs_nan (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int)
    (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
    (s : Bool) (payload : Nat),
    impl.flocq.babs prec emax nanH (BinaryFloat.nan s payload) =
      nanH (BinaryFloat.nan s payload)

/-- `babs` clears the sign of finite inputs. -/
def spec_babs_finite (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int)
    (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
    (s : Bool) (m : Nat) (e : Int),
    impl.flocq.babs prec emax nanH (BinaryFloat.finite s m e) =
      BinaryFloat.finite false m e

/-- `babs` maps any signed zero to positive zero. -/
def spec_babs_zero (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int)
    (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
    (s : Bool),
    impl.flocq.babs prec emax nanH (BinaryFloat.zero s) = BinaryFloat.zero false

/-- `bmaxFloat` uses the all-ones precision mantissa and maximal exponent. -/
def spec_bmaxFloat_def (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) (s : Bool),
    impl.flocq.bmaxFloat prec emax s =
      BinaryFloat.finite s ((2 : Nat) ^ prec.toNat - 1) (emax - prec)

/-- `bopp` delegates NaN inputs to the supplied NaN handler. -/
def spec_bopp_nan (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int)
    (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
    (s : Bool) (payload : Nat),
    impl.flocq.bopp prec emax nanH (BinaryFloat.nan s payload) =
      nanH (BinaryFloat.nan s payload)

/-- `bopp` flips finite input signs. -/
def spec_bopp_finite (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int)
    (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
    (s : Bool) (m : Nat) (e : Int),
    impl.flocq.bopp prec emax nanH (BinaryFloat.finite s m e) =
      BinaryFloat.finite (!s) m e

/-- `bopp` flips zero signs. -/
def spec_bopp_zero (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int)
    (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
    (s : Bool),
    impl.flocq.bopp prec emax nanH (BinaryFloat.zero s) = BinaryFloat.zero (!s)

/-- IEEE addition is correct on finite inputs: the real value of the result
    equals `rndFLT(bR(x) + bR(y))`. -/
def spec_Bplus_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec]
  (mode : RoundingMode)
  (nanH : BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax)
  (x y : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true → impl.flocq.isFinite prec emax y = true →
  impl.flocq.b2R prec emax (impl.flocq.bplus prec emax mode nanH x y) =
    rndFLT prec emax mode (impl.flocq.b2R prec emax x + impl.flocq.b2R prec emax y)

/-- IEEE subtraction is correct on finite inputs: the real value of the result
    equals `rndFLT(bR(x) − bR(y))`. -/
def spec_Bminus_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec]
  (mode : RoundingMode)
  (nanH : BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax)
  (x y : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true → impl.flocq.isFinite prec emax y = true →
  impl.flocq.b2R prec emax (impl.flocq.bminus prec emax mode nanH x y) =
    rndFLT prec emax mode (impl.flocq.b2R prec emax x - impl.flocq.b2R prec emax y)

/-- IEEE multiplication is correct on finite inputs: the real value of the
    result equals `rndFLT(bR(x) * bR(y))`. -/
def spec_Bmult_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec]
  (mode : RoundingMode)
  (nanH : BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax)
  (x y : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true → impl.flocq.isFinite prec emax y = true →
  impl.flocq.b2R prec emax (impl.flocq.bmult prec emax mode nanH x y) =
    rndFLT prec emax mode (impl.flocq.b2R prec emax x * impl.flocq.b2R prec emax y)

/-- IEEE division is correct on finite inputs with non-zero divisor:
    the real value of the result equals `rndFLT(bR(x) / bR(y))`. -/
def spec_Bdiv_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec]
  (mode : RoundingMode)
  (nanH : BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax)
  (x y : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true → impl.flocq.isFinite prec emax y = true →
  impl.flocq.b2R prec emax y ≠ 0 →
  impl.flocq.b2R prec emax (impl.flocq.bdiv prec emax mode nanH x y) =
    rndFLT prec emax mode (impl.flocq.b2R prec emax x / impl.flocq.b2R prec emax y)

/-- IEEE square root is correct on finite non-negative inputs:
    the real value of the result equals `rndFLT(√bR(x))`. -/
def spec_Bsqrt_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec]
  (mode : RoundingMode)
  (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
  (x : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true → (0 : ℝ) ≤ impl.flocq.b2R prec emax x →
  impl.flocq.b2R prec emax (impl.flocq.bsqrt prec emax mode nanH x) =
    rndFLT prec emax mode (Real.sqrt (impl.flocq.b2R prec emax x))

/-- IEEE fused multiply-add is correct on finite inputs:
    the real value of the result equals `rndFLT(bR(x)*bR(y) + bR(z))`. -/
def spec_Bfma_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec]
  (mode : RoundingMode)
  (nanH : BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax → BinaryFloat prec emax)
  (x y z : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true → impl.flocq.isFinite prec emax y = true → impl.flocq.isFinite prec emax z = true →
  impl.flocq.b2R prec emax (impl.flocq.bfma prec emax mode nanH x y z) =
    rndFLT prec emax mode (impl.flocq.b2R prec emax x * impl.flocq.b2R prec emax y + impl.flocq.b2R prec emax z)

/-- `bldexp` scales a finite float by a power of 2:
    the real value of the result equals `rndFLT(bR(x) * 2^e)`. -/
def spec_Bldexp_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec]
  (mode : RoundingMode) (x : BinaryFloat prec emax) (e : Int),
  impl.flocq.isFinite prec emax x = true →
  impl.flocq.b2R prec emax (impl.flocq.bldexp prec emax mode x e) =
    rndFLT prec emax mode (impl.flocq.b2R prec emax x * Flocq.bpow radix2 e)

/-- `bfrexp` decomposes a finite (non-unit) float into significand and exponent:
    `bR(x) = bR(m) * 2^e` with `1/2 ≤ |bR(m)| < 1`. -/
def spec_Bfrexp_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec] (x : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true → x ≠ impl.flocq.bone prec emax →
  let (m, e) := impl.flocq.bfrexp prec emax x
  impl.flocq.b2R prec emax x = impl.flocq.b2R prec emax m * Flocq.bpow radix2 e ∧
  (1 : ℝ) / 2 ≤ |impl.flocq.b2R prec emax m| ∧ |impl.flocq.b2R prec emax m| < 1

/-- `bcompare` on finite inputs returns the three-way comparison of their
    real values.  Mirrors upstream `Bcompare_correct`, which requires both
    operands to be finite (not merely non-NaN): `b2R` collapses `±∞` to `0`, so
    an infinity input under a weaker non-NaN guard would spuriously compare
    against `0` while `bcompare` returns the correct infinity ordering. -/
def spec_Bcompare_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) (x y : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true → impl.flocq.isFinite prec emax y = true →
  impl.flocq.bcompare prec emax x y = some (Rcompare (impl.flocq.b2R prec emax x) (impl.flocq.b2R prec emax y))

/-- `bnearbyint` on a finite input rounds to an integer float:
    the real value of the result equals `roundMode(mode, bR(x))`. -/
def spec_Bnearbyint_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec]
  (mode : RoundingMode) (x : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true →
  impl.flocq.b2R prec emax (impl.flocq.bnearbyint prec emax mode x) =
    (impl.flocq.roundMode mode (impl.flocq.b2R prec emax x) : ℝ)

/-- `btrunc` on a finite input truncates toward zero:
    the real value of the result equals `Ztrunc(bR(x))`. -/
def spec_Btrunc_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) (x : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true →
  impl.flocq.b2R prec emax (impl.flocq.btrunc prec emax x) = (Ztrunc (impl.flocq.b2R prec emax x) : ℝ)

/-- `bone` represents the float 1.0: its real value is 1. -/
def spec_Bone_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec],
  impl.flocq.b2R prec emax (impl.flocq.bone prec emax) = 1

/-- `bsucc` on a finite float gives the next representable float above it:
    its real value equals `succ(bR(x))` in the FLT format. -/
def spec_Bsucc_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec] (x : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true →
  impl.flocq.b2R prec emax (impl.flocq.bsucc prec emax x) =
    Flocq.succ radix2 (FLT_exp (2 - prec - emax) prec) (impl.flocq.b2R prec emax x)

/-- `bpred` on a finite float gives the previous representable float:
    its real value equals `pred(bR(x))` in the FLT format. -/
def spec_Bpred_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec] (x : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true →
  impl.flocq.b2R prec emax (impl.flocq.bpred prec emax x) =
    Flocq.pred radix2 (FLT_exp (2 - prec - emax) prec) (impl.flocq.b2R prec emax x)

/-- `bulp` on a finite non-zero float gives the unit in the last place:
    its real value equals `ulp(bR(x))` in the FLT format. -/
def spec_Bulp_correct (impl : RepoImpl) : Prop :=
  ∀ (prec emax : Int) [PrecGt0 prec] (x : BinaryFloat prec emax),
  impl.flocq.isFinite prec emax x = true → impl.flocq.b2R prec emax x ≠ 0 →
  impl.flocq.b2R prec emax (impl.flocq.bulp prec emax x) =
    Flocq.ulp radix2 (FLT_exp (2 - prec - emax) prec) (impl.flocq.b2R prec emax x)
