import Flocq.Harness
import Flocq.Prop.Impl.Sterbenz

/-!
# Flocq.Prop.Spec.Sterbenz

Specifications for the Sterbenz exact subtraction theorem and the same-sign
exact addition theorem, corresponding to key theorems from
`src/Prop/Sterbenz.v`.

Both specs assert pure mathematical properties about `genericFormat` and do not
reference any computable API function — they are universally quantified over the
format parameters `beta` and `fexp`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Sterbenz lemma: if `y/2 ≤ x ≤ 2*y` and both `x`, `y` are in generic
    floating-point format, then `x − y` is also in generic format (i.e., the
    subtraction is exact).
    Mirrors Coq's `sterbenz` theorem from `src/Prop/Sterbenz.v`. -/
def spec_sterbenz (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int)
  [ValidExp fexp] [MonotoneExp fexp]
  (x y : ℝ),
  genericFormat beta fexp x → genericFormat beta fexp y →
  y / 2 ≤ x → x ≤ 2 * y →
  genericFormat beta fexp (x - y)

/-- Exact addition with same-sign operands: if `x` and `y` are in generic
    floating-point format and have the same sign (both non-negative or both
    non-positive), then `x + y` is also in generic format.
    Corresponds to `generic_format_plus` (restated via `generic_format_plus_weak`)
    from `src/Prop/Sterbenz.v`. -/
def spec_genericFormatPlus (impl : RepoImpl) : Prop :=
  ∀ (beta : Radix) (fexp : Int → Int)
  [ValidExp fexp] [MonotoneExp fexp]
  (x y : ℝ),
  genericFormat beta fexp x → genericFormat beta fexp y →
  (0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0) →
  genericFormat beta fexp (x + y)
