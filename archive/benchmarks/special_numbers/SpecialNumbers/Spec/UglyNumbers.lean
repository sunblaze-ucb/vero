import SpecialNumbers.Harness

/-!
# SpecialNumbers.Spec.UglyNumbers

Specifications for ugly numbers.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- The nth ugly number is the last element of the Hamming prefix of length n. -/
def spec_ugly_agrees_with_hamming (impl : RepoImpl) : Prop :=
  ∀ n : Int, n > 0 →
    ((impl.specialNumbers.hamming n).map Int.ofNat).getLast? =
      some (impl.specialNumbers.ugly_numbers n)
