import VestV2.Impl.RegularSuccess
import VestV2.Harness

/-!
# VestV2.Spec.RegularSuccess

Specifications for the Success combinator module. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- successParse always returns Ok(0, ()) for any input. -/
def spec_success_always_succeeds (impl : RepoImpl) : Prop :=
  ∀ (s : List UInt8), impl.vest.successParse s = Except.ok (0, ())

/-- successSerialize always returns 0 bytes written. -/
def spec_success_serialize_zero (impl : RepoImpl) : Prop :=
  ∀ (buf : List UInt8) (pos : Nat),
    pos ≤ buf.length → impl.vest.successSerialize () buf pos = Except.ok 0
