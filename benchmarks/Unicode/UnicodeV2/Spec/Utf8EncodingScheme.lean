import UnicodeV2.Harness

/-!
# Unicode.Spec.Utf8EncodingScheme

Specifications for the UTF-8 encoding scheme. Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`; theorem stubs live in
`Unicode/Proof/Utf8EncodingScheme.lean`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Serializing a code unit sequence and then deserializing the result yields the
    original code unit sequence. -/
def spec_serialize_deserialize (impl : RepoImpl) : Prop :=
  ∀ (s : List Utf8CodeUnit),
    impl.unicodeV2.deserialize (impl.unicodeV2.serialize s) = s

/-- Deserializing a byte sequence and then serializing the result yields the original
    byte sequence. -/
def spec_deserialize_serialize (impl : RepoImpl) : Prop :=
  ∀ (b : List Utf8Byte),
    impl.unicodeV2.serialize (impl.unicodeV2.deserialize b) = b
