import VestV2.Impl.RegularEnd
import VestV2.Harness

/-!
# VestV2.Spec.RegularEnd

Specifications for the End combinator module. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- End satisfies the SecureSpecCombinator contract: serialize then parse
    is identity, parse then serialize returns the consumed prefix, and
    parse fails iff input is non-empty. -/
def spec_end_secure_combinator (_impl : RepoImpl) : Prop :=
  (∀ (v : Unit), End.spec_parse End.mk (End.spec_serialize End.mk v) = some (0, ())) ∧
  (End.spec_parse End.mk [] = some (0, ())) ∧
  (∀ (s : List UInt8), s ≠ [] → End.spec_parse End.mk s = none)

/-- The exec endParse returns Ok(0, ()) iff the input is empty, and
    returns Err(NotEof) otherwise. -/
def spec_end_parse_correct (impl : RepoImpl) : Prop :=
  (impl.vest.endParse [] = Except.ok (0, ())) ∧
  (∀ (s : List UInt8), s ≠ [] → impl.vest.endParse s = Except.error ParseError.NotEof)

/-- endSerialize always succeeds and reports that it writes zero bytes. -/
def spec_end_serialize_zero (impl : RepoImpl) : Prop :=
  ∀ (buf : List UInt8) (pos : Nat),
    impl.vest.endSerialize () buf pos = Except.ok 0
