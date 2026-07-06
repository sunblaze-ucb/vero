import Eth20Dafny.Harness

/-!
# Eth20Dafny.Spec.SszIntSeDes

Specifications for integer serialization and deserialization. Each
`spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Source-backed Dafny specification `IntSeDes.involution`. -/
def spec_involution (impl : RepoImpl) : Prop :=
  ∀ (n : Nat) (k : Nat),
    1 ≤ k →
    n < Eth20Dafny.power2 (8 * k) →
    impl.eth2Dafny.uintDes (impl.eth2Dafny.uintSe n k) = n
