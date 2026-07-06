import Flocq.Harness
import Flocq.Prop.Impl.Relative

open Flocq

/-!
# Flocq.Prop.Spec.Relative

Relative error bounds for generic floating-point rounding, corresponding to
key theorems from `src/Prop/Relative.v`.

The three specs cover:
- `spec_relativeError` — round-down error < beta^(fexp ex) when |x| is in a binade.
- `spec_relativeErrorN` — nearest-rounding error ≤ half a ULP in the same setting.
- `spec_errorNFLT` — FLT nearest-rounding error bounded by the max of an
  absolute term and a relative term.

These are purely mathematical properties of the axiomatized `round` and `bpow`
functions; no `impl.flocq.*` fields are needed.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Absolute rounding error (round-down) is bounded by beta^(fexp(ex)):
    if beta^(ex-1) ≤ |x| then |round_DN(x) − x| < beta^(fexp(ex)).
    Mirrors Coq's `error_lt_ulp` specialised to round-down and a binade hypothesis. -/
def spec_relativeError (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (x : ℝ) (_ : x ≠ 0) (ex : Int) (_ : bpow beta (ex - 1) ≤ |x|),
  |round beta fexp Rounding.DN x - x| < bpow beta (fexp ex)

/-- Rounding-to-nearest error is bounded by half a ULP:
    if beta^(ex-1) ≤ |x| then |round_NE(x) − x| ≤ beta^(fexp(ex)) / 2.
    Mirrors Coq's `error_le_half_ulp` with the binade hypothesis. -/
def spec_relativeErrorN (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp]
  (x : ℝ) (_ : x ≠ 0) (ex : Int) (_ : bpow beta (ex - 1) ≤ |x|),
  |round beta fexp Rounding.NE x - x| ≤ bpow beta (fexp ex) / 2

/-- FLT rounding-to-nearest error: bounded by the max of an absolute term
    (beta^(emin+prec-1) * beta^(1-prec) / 2) and a relative term (|x| * beta^(1-prec) / 2).
    Mirrors Coq's `error_N_FLT` (combined absolute+relative error bound). -/
def spec_errorNFLT (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (emin prec : Int) (_ : 0 < prec) (x : ℝ),
  |round beta (FLT_exp emin prec) Rounding.NE x - x|
    ≤ max (bpow beta (emin + prec - 1) * bpow beta (1 - prec) / 2)
          (|x| * bpow beta (1 - prec) / 2)
