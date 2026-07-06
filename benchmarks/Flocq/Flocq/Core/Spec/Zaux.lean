import Flocq.Harness

/-!
# Flocq.Core.Spec.Zaux

Specifications for `Core.Zaux` foundation types. Each `spec_*` would be a
property over an arbitrary `impl : RepoImpl`; theorem stubs live in the
corresponding `Proof/` files (generated downstream).

`Core.Zaux` provides the `Radix` type used throughout Flocq plus selected
integer power, Euclidean-division, and iteration helpers.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `zfastPowPos` computes the zeroth power as one. -/
def spec_zfastPowPos_zero (impl : RepoImpl) : Prop :=
  ∀ (v : Int), impl.flocq.zfastPowPos v 0 = 1

/-- `zfastPowPos` follows the usual successor equation for powers. -/
def spec_zfastPowPos_succ (impl : RepoImpl) : Prop :=
  ∀ (v : Int) (n : Nat),
    impl.flocq.zfastPowPos v (n + 1) = impl.flocq.zfastPowPos v n * v

/-- Source-name correctness spec for positive integer exponentiation. -/
def spec_Zfast_pow_pos_correct (impl : RepoImpl) : Prop :=
  ∀ (v : Int) (n : Nat), impl.flocq.zfastPowPos v n = v ^ n

/-- `zposDivEuclAux1` returns Lean's quotient component. -/
def spec_zposDivEuclAux1_quot (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), (impl.flocq.zposDivEuclAux1 a b).1 = Int.ediv a b

/-- `zposDivEuclAux1` returns Lean's remainder component. -/
def spec_zposDivEuclAux1_rem (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), (impl.flocq.zposDivEuclAux1 a b).2 = Int.emod a b

/-- `zposDivEuclAux` handles the `a < b` fast path. -/
def spec_zposDivEuclAux_small (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), a < b → impl.flocq.zposDivEuclAux a b = (0, a)

/-- `zposDivEuclAux` handles the `a = b` fast path. -/
def spec_zposDivEuclAux_equal (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), a = b → ¬ a < b → impl.flocq.zposDivEuclAux a b = (1, 0)

/-- `zfastDivEucl` returns Lean's quotient component. -/
def spec_zfastDivEucl_quot (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), (impl.flocq.zfastDivEucl a b).1 = Int.ediv a b

/-- `zfastDivEucl` returns Lean's remainder component. -/
def spec_zfastDivEucl_rem (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), (impl.flocq.zfastDivEucl a b).2 = Int.emod a b

/-- Source-name correctness spec for Euclidean division. -/
def spec_Zfast_div_eucl_correct (impl : RepoImpl) : Prop :=
  ∀ (a b : Int), impl.flocq.zfastDivEucl a b = (Int.ediv a b, Int.emod a b)

/-- `iterNat` with zero iterations is the identity. -/
def spec_iterNat_zero (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (f : α → α) (x : α), impl.flocq.iterNat f 0 x = x

/-- `iterNat` with one additional iteration applies the function first. -/
def spec_iterNat_succ (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (f : α → α) (n : Nat) (x : α),
    impl.flocq.iterNat f (n + 1) x = impl.flocq.iterNat f n (f x)
