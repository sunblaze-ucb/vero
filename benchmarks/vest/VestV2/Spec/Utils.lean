import VestV2.Harness

/-!
# VestV2.Spec.Utils

Specifications for utility helper functions. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- setRange splices input into data at position i, preserving the prefix and suffix. -/
def spec_set_range_correct (impl : RepoImpl) : Prop :=
  ∀ (data input : List UInt8) (i : Nat),
    i + input.length ≤ data.length →
    let r := impl.vest.setRange data i input
    r = data.take i ++ input ++ data.drop (i + input.length)

/-- compareSlice returns byte-list equality, not just reflexive truth. -/
def spec_compare_slice_correct (impl : RepoImpl) : Prop :=
  ∀ (x y : List UInt8), impl.vest.compareSlice x y = (x == y)

/-- initVecU8 n produces a list of exactly n zeros. -/
def spec_init_vec_u8_length (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), (impl.vest.initVecU8 n).length = n ∧
    ∀ i, i < n → (impl.vest.initVecU8 n)[i]? = some 0
