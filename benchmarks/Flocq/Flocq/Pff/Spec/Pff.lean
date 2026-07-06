import Flocq.Harness
import Flocq.Pff.Impl.Pff

/-!
# Flocq.Pff.Spec.Pff

Curated source-backed specifications for selected Pff APIs. These preserve the
useful behavior contracts from the rerun without importing the incompatible
generated module layout wholesale.
-/

def spec_pffFopp_num (impl : RepoImpl) : Prop :=
  ∀ x : PffFloat, (impl.flocq.pffFopp x).num = -x.num

def spec_pffFopp_exp (impl : RepoImpl) : Prop :=
  ∀ x : PffFloat, (impl.flocq.pffFopp x).exp = x.exp

def spec_pffFabs_num (impl : RepoImpl) : Prop :=
  ∀ x : PffFloat, (impl.flocq.pffFabs x).num = pffAbs x.num

def spec_pffFabs_exp (impl : RepoImpl) : Prop :=
  ∀ x : PffFloat, (impl.flocq.pffFabs x).exp = x.exp

def spec_pffFplus_zero_left (impl : RepoImpl) : Prop :=
  ∀ x : PffFloat, impl.flocq.pffFplus { num := 0, exp := x.exp } x = x

def spec_pffFplus_zero_right (impl : RepoImpl) : Prop :=
  ∀ x : PffFloat, impl.flocq.pffFplus x { num := 0, exp := x.exp } = x

def spec_pffFmult_num (impl : RepoImpl) : Prop :=
  ∀ x y : PffFloat, (impl.flocq.pffFmult x y).num = x.num * y.num

def spec_pffFmult_exp (impl : RepoImpl) : Prop :=
  ∀ x y : PffFloat, (impl.flocq.pffFmult x y).exp = x.exp + y.exp

def spec_pffMZlistAux_mem (impl : RepoImpl) : Prop :=
  ∀ (start : Int) (n : Nat) (k : Nat),
    k <= n → start + Int.ofNat k ∈ impl.flocq.pffMZlistAux start n

def spec_pffMZlist_mem (impl : RepoImpl) : Prop :=
  ∀ lo hi r : Int,
    lo <= r → r <= hi → r ∈ impl.flocq.pffMZlist lo hi

def spec_pffMProd_mem (impl : RepoImpl) : Prop :=
  ∀ (A B : Type) (xs : List A) (ys : List B) (x : A) (y : B),
    x ∈ xs → y ∈ ys → (x, y) ∈ impl.flocq.pffMProd A B xs ys
