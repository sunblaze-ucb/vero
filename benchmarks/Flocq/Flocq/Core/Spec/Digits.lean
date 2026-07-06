import Flocq.Harness

/-!
# Flocq.Core.Spec.Digits

Specifications for the `zdigits` digit-counting function.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

These specs correspond to key theorems from the Coq source `src/Core/Digits.v`:
`Zdigits_correct`, `Zdigits_ge_0`, `Zdigits_gt_0`, and `Zdigits_opp`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `digits2Pnat` returns zero exactly on zero. -/
def spec_digits2Pnat_zero (impl : RepoImpl) : Prop :=
  impl.flocq.digits2Pnat 0 = 0

/-- `digits2Pnat` is positive on positive natural inputs. -/
def spec_digits2Pnat_pos (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), n ≠ 0 → 0 < impl.flocq.digits2Pnat n

/-- `zsumDigit` is the linear repeated-digit contribution helper. -/
def spec_zsumDigit_def (impl : RepoImpl) : Prop :=
  ∀ (digit k : Int), impl.flocq.zsumDigit digit k = digit * k

/-- `zscale` with zero exponent is the identity. -/
def spec_zscale_zero (impl : RepoImpl) : Prop :=
  ∀ (r : Radix) (n : Int), impl.flocq.zscale r n 0 = n

/-- `zscale` with a positive exponent multiplies by the radix power. -/
def spec_zscale_nonneg (impl : RepoImpl) : Prop :=
  ∀ (r : Radix) (n k : Int), 0 ≤ k →
    impl.flocq.zscale r n k = n * (r.val ^ k.toNat)

/-- Degenerate slices are empty. -/
def spec_zslice_empty (impl : RepoImpl) : Prop :=
  ∀ (r : Radix) (n k1 k2 : Int), k2 ≤ k1 → impl.flocq.zslice r n k1 k2 = 0

/-- `zdigitsAux` exposes the fuelled helper used by `zdigits`. -/
def spec_zdigitsAux_def (impl : RepoImpl) : Prop :=
  ∀ (absN beta nb pow : Int) (fuel : Nat),
    impl.flocq.zdigitsAux absN beta nb pow fuel = zdigitsAuxCore absN beta nb pow fuel

/-- `zdigits r 0 = 0`: zero has zero digits in any radix. -/
def spec_zdigits_zero (impl : RepoImpl) : Prop :=
  ∀ (r : Radix), impl.flocq.zdigits r 0 = 0

/-- `zdigits` always returns a non-negative value. -/
def spec_zdigits_nonneg (impl : RepoImpl) : Prop :=
  ∀ (r : Radix) (n : Int), 0 ≤ impl.flocq.zdigits r n

/-- For any nonzero integer, `zdigits` returns a strictly positive value. -/
def spec_zdigits_pos (impl : RepoImpl) : Prop :=
  ∀ (r : Radix) (n : Int), n ≠ 0 → 0 < impl.flocq.zdigits r n

/-- `zdigits` is invariant under negation: the digit count of `n` and `-n` agree. -/
def spec_zdigits_opp (impl : RepoImpl) : Prop :=
  ∀ (r : Radix) (n : Int), impl.flocq.zdigits r (-n) = impl.flocq.zdigits r n

/-- Upper bound: `|n| < β^(zdigits r n)`.
    Holds universally — vacuously for n = 0 since 0 < β^0 = 1. -/
def spec_zdigits_correct_upper (impl : RepoImpl) : Prop :=
  ∀ (r : Radix) (n : Int),
    n.natAbs < r.val.natAbs ^ (impl.flocq.zdigits r n).natAbs

/-- Lower bound: for n ≠ 0, `β^(zdigits r n − 1) ≤ |n|`. -/
def spec_zdigits_correct_lower (impl : RepoImpl) : Prop :=
  ∀ (r : Radix) (n : Int), n ≠ 0 →
    r.val.natAbs ^ ((impl.flocq.zdigits r n).natAbs - 1) ≤ n.natAbs
