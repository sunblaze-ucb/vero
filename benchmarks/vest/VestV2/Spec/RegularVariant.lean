import VestV2.Impl.RegularVariant
import VestV2.Harness

/-!
# VestV2.Spec.RegularVariant

Specifications for variant combinator operations. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- When fst successfully parses, Choice returns the Left result regardless of snd. -/
def spec_choice_left_parse (_impl : RepoImpl) : Prop :=
  ∀ (F S A B : Type) [SpecCombinator F A] [SpecCombinator S B]
    (c : Choice F S) (s : List UInt8) (n : Int) (v : A),
  SpecCombinator.spec_parse c.fst s = some (n, v) →
  Choice.spec_parse c s = some (n, Either.Left v)

/-- When fst fails and snd succeeds, Choice returns the Right result. -/
def spec_choice_right_parse (_impl : RepoImpl) : Prop :=
  ∀ (F S A B : Type) [SpecCombinator F A] [SpecCombinator S B]
    (c : Choice F S) (s : List UInt8) (n : Int) (v : B),
  SpecCombinator.spec_parse c.fst s = none →
  SpecCombinator.spec_parse c.snd s = some (n, v) →
  Choice.spec_parse c s = some (n, Either.Right v)
