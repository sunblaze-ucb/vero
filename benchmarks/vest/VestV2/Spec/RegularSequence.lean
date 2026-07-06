import VestV2.Impl.RegularSequence
import VestV2.Harness

/-!
# VestV2.Spec.RegularSequence

Specifications for sequential combinators. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Pair combinator is roundtrip correct when both inner combinators are
    prefix-secure and roundtrip correct. -/
def spec_pair_roundtrip (_impl : RepoImpl) : Prop :=
  ∀ (F S A B : Type) [SpecCombinator F A] [SpecCombinator S B] (c : SpecPair F S) (va : A) (vb : B),
  SpecPair.spec_parse c (SpecPair.spec_serialize c (va, vb)) =
    some (↑((SpecCombinator.spec_serialize c.fst va).length +
            (SpecCombinator.spec_serialize c.snd vb).length), (va, vb))
