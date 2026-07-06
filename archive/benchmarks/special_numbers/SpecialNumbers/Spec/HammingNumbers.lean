import SpecialNumbers.Harness
import SpecialNumbers.Spec.Aux

/-!
# SpecialNumbers.Spec.HammingNumbers

Specifications for Hamming numbers.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Hamming prefixes contain positive values in strictly increasing order. -/
def spec_hamming_sequence_shape (impl : RepoImpl) : Prop :=
  ∀ n : Int, n > 0 →
    aux_allPositive ((impl.specialNumbers.hamming n).map Int.ofNat) ∧
    aux_sortedStrict ((impl.specialNumbers.hamming n).map Int.ofNat)

/-- For non-negative `k`, `(hamming k).length = k.toNat`: the impl produces exactly
    `k` Hamming numbers (and `0` for `k = 0`). Length law not implied by sequence-shape. -/
def spec_hamming_length (impl : RepoImpl) : Prop :=
  ∀ k : Int, k ≥ 0 → (impl.specialNumbers.hamming k).length = k.toNat
