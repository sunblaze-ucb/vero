import VestV2.Impl.RegularFail
import VestV2.Harness

/-!
# VestV2.Spec.RegularFail

Specifications for the Fail combinator module. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- failParse always returns an Err, never Ok, for any input. -/
def spec_fail_always_fails (impl : RepoImpl) : Prop :=
  ∀ (s : List UInt8), ∃ e, impl.vest.failParse s = Except.error e

/-- failSerialize is unreachable in practice and always returns an error. -/
def spec_fail_serialize_always_fails (impl : RepoImpl) : Prop :=
  ∀ (buf : List UInt8) (pos : Nat),
    ∃ e, impl.vest.failSerialize () buf pos = Except.error e
