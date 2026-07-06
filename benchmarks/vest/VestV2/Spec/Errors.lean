import VestV2.Impl.Errors
import VestV2.Harness

/-!
# VestV2.Spec.Errors

Specifications for the Errors module.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- fromParseError wraps any parser error in the shared Error sum. -/
def spec_from_parse_error_correct (impl : RepoImpl) : Prop :=
  ∀ (e : ParseError), impl.vest.fromParseError e = Error.Parse e

/-- fromSerializeError wraps any serializer error in the shared Error sum. -/
def spec_from_serialize_error_correct (impl : RepoImpl) : Prop :=
  ∀ (e : SerializeError), impl.vest.fromSerializeError e = Error.Serialize e
