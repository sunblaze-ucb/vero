import Flocq.Harness
import Flocq.Core.Impl.Ulp

open Flocq

/-!
# Flocq.Core.Spec.Raux

Specifications for the base-power function `bpow` defined in
`Impl/Core.Raux.lean`, corresponding to key theorems from
`src/Core/Raux.v`.

The specs cover:
- Non-negativity of `bpow`
- The magnitude of `beta^e` equals `e + 1`
- Monotonicity of `mag` with respect to absolute value

All specs access the `bpow` API via `impl.flocq.bpow` through `RepoImpl`.
`mag` refers to the axiomatized `Flocq.mag` from `Core.Ulp`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `rcompare` exposes the three-way real comparison helper. -/
def spec_rcompare_def (impl : RepoImpl) : Prop :=
  ∀ (x y : ℝ), impl.flocq.rcompare x y = Rcompare x y

/-- Source-name version of `Rcompare_spec`: lt/eq/gt reflect the real order. -/
def spec_Rcompare_spec (impl : RepoImpl) : Prop :=
  ∀ (x y : ℝ),
    match impl.flocq.rcompare x y with
    | Ordering.lt => x < y
    | Ordering.eq => x = y
    | Ordering.gt => y < x

/-- `rleBool` is true exactly on `x ≤ y`. -/
def spec_rleBool_def (impl : RepoImpl) : Prop :=
  ∀ (x y : ℝ), impl.flocq.rleBool x y = (if x ≤ y then true else false)

/-- Source-name version of `Rle_bool_spec`. -/
def spec_Rle_bool_spec (impl : RepoImpl) : Prop :=
  ∀ (x y : ℝ), impl.flocq.rleBool x y = true ↔ x ≤ y

/-- `rltBool` is true exactly on `x < y`. -/
def spec_rltBool_def (impl : RepoImpl) : Prop :=
  ∀ (x y : ℝ), impl.flocq.rltBool x y = (if x < y then true else false)

/-- Source-name version of `Rlt_bool_spec`. -/
def spec_Rlt_bool_spec (impl : RepoImpl) : Prop :=
  ∀ (x y : ℝ), impl.flocq.rltBool x y = true ↔ x < y

/-- `reqBool` is true exactly on equality. -/
def spec_reqBool_def (impl : RepoImpl) : Prop :=
  ∀ (x y : ℝ), impl.flocq.reqBool x y = (if x = y then true else false)

/-- Source-name version of `Req_bool_spec`. -/
def spec_Req_bool_spec (impl : RepoImpl) : Prop :=
  ∀ (x y : ℝ), impl.flocq.reqBool x y = true ↔ x = y

/-- `ztrunc` exposes truncation toward zero. -/
def spec_ztrunc_def (impl : RepoImpl) : Prop :=
  ∀ (x : ℝ), impl.flocq.ztrunc x = Ztrunc x

/-- `zaway` exposes rounding away from zero. -/
def spec_zaway_def (impl : RepoImpl) : Prop :=
  ∀ (x : ℝ), impl.flocq.zaway x = Zaway x

/-- `condRopp true` negates the input. -/
def spec_condRopp_true (impl : RepoImpl) : Prop :=
  ∀ (x : ℝ), impl.flocq.condRopp true x = -x

/-- `condRopp false` leaves the input unchanged. -/
def spec_condRopp_false (impl : RepoImpl) : Prop :=
  ∀ (x : ℝ), impl.flocq.condRopp false x = x

/-- `bpow beta e` is always non-negative. -/
def spec_bpow_ge_0 (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (e : Int), (0 : ℝ) ≤ impl.flocq.bpow beta e

/-- The magnitude of `beta^e` is `e + 1`. -/
def spec_mag_bpow (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (e : Int), Flocq.mag beta (impl.flocq.bpow beta e) = e + 1

/-- If `|x| ≤ |y|` and `x ≠ 0` then `mag beta x ≤ mag beta y`. -/
def spec_mag_le_abs (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (x y : ℝ), x ≠ 0 → |x| ≤ |y| → Flocq.mag beta x ≤ Flocq.mag beta y
