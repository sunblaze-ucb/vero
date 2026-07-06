import VestV2.Impl.RegularRepetition
import VestV2.Harness

/-!
# VestV2.Spec.RegularRepetition

Specifications for the RegularRepetition module. Each `spec_*` is a
property that does not depend on `impl : RepoImpl` (pure spec-helper
properties).

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- RepeatN satisfies the serialize-then-parse roundtrip: parsing the
    serialized output of n inner values returns the original list. -/
def spec_repetition_repeatn_roundtrip (_impl : RepoImpl) : Prop :=
  ∀ (Inner T : Type) [SpecCombinator Inner T] (c : RepeatN Inner) (vs : List T),
  vs.length = c.n →
  RepeatN.spec_parse c (vs.flatMap (SpecCombinator.spec_serialize c.inner)) =
    some ((vs.foldl (fun acc v => acc + (SpecCombinator.spec_serialize c.inner v).length) 0 : Int), vs)
