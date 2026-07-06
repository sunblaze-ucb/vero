import Flocq.Harness

/-!
# Flocq.Core.Spec.FLT

Specifications for the FLT (floating-point with gradual underflow / subnormals)
format module. Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

The first three specs relate the FLT format to the FLX (no-underflow) format:

* `spec_cexp_FLT_FLX` — when |x| is large enough, the FLT and FLX canonical
  exponents coincide.
* `spec_generic_format_FLX_FLT` — every FLT-representable number is also
  FLX-representable.
* `spec_round_FLT_FLX` — when |x| is large enough, rounding in FLT and FLX
  give the same result.

The last two specs describe the unit in the last place (`ulp`) in the FLT
format:

* `spec_ulp_FLT_0` — the ulp of 0 under the FLT exponent is `beta^emin`.
* `spec_ulp_FLT_small` — for any |x| below `beta^(emin+prec)` the ulp equals
  `beta^emin`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- When |x| ≥ beta^(emin+prec-1) the FLT and FLX canonical exponents agree. -/
def spec_cexp_FLT_FLX (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (emin prec : Int) [PrecGt0 prec] (x : ℝ),
    Flocq.bpow beta (emin + prec - 1) ≤ |x| →
    cexp beta (FLT_exp emin prec) x = cexp beta (FLX_exp prec) x

/-- Every FLT-format number is also an FLX-format number. -/
def spec_generic_format_FLX_FLT (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (emin prec : Int) [PrecGt0 prec] (x : ℝ),
    genericFormat beta (FLT_exp emin prec) x → genericFormat beta (FLX_exp prec) x

/-- When |x| ≥ beta^(emin+prec-1) rounding in FLT and FLX gives the same result. -/
def spec_round_FLT_FLX (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (emin prec : Int) [PrecGt0 prec]
    (rnd : ℝ → Int) [ValidRnd rnd] (x : ℝ),
    Flocq.bpow beta (emin + prec - 1) ≤ |x| →
    Flocq.round beta (FLT_exp emin prec) rnd x =
    Flocq.round beta (FLX_exp prec) rnd x

/-- The ulp of 0 in FLT format is beta^emin. -/
def spec_ulp_FLT_0 (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (emin prec : Int) [PrecGt0 prec],
    impl.flocq.ulp beta (FLT_exp emin prec) 0 = Flocq.bpow beta emin

/-- For |x| < beta^(emin+prec) the ulp in FLT format equals beta^emin. -/
def spec_ulp_FLT_small (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (emin prec : Int) [PrecGt0 prec] (x : ℝ),
    |x| < Flocq.bpow beta (emin + prec) →
    impl.flocq.ulp beta (FLT_exp emin prec) x = Flocq.bpow beta emin
