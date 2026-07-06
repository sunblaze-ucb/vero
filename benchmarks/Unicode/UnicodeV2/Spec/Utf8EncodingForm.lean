import UnicodeV2.Harness

/-!
# Unicode.Spec.Utf8EncodingForm

Specifications for the UTF-8 encoding form. Each `spec_*` is a property over
an arbitrary `impl : RepoImpl`. Specs access API functions via
`impl.unicodeV2.<fn>` where `unicode` is the `UnicodeV2Bundled` field of `RepoImpl`.

Based on the invariants in Unicode 14.0 Table 3-6 and Table 3-7 and the
round-trip guarantees documented in `Utf8EncodingForm.dfy`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

namespace Utf8

/-- Encoding a scalar value and then decoding the result yields the original
    scalar value (encode-then-decode round-trip). -/
def spec_encode_decode_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (v : ScalarValue),
    impl.unicodeV2.utf8DecodeMinimalWellFormedCodeUnitSubsequence
      (impl.unicodeV2.utf8EncodeScalarValue v) = v

/-- The byte sequence produced by encoding a scalar value is a minimal
    well-formed UTF-8 code unit subsequence. -/
def spec_encode_is_well_formed (impl : RepoImpl) : Prop :=
  ∀ (v : ScalarValue),
    impl.unicodeV2.utf8IsMinimalWellFormedCodeUnitSubsequence
      (impl.unicodeV2.utf8EncodeScalarValue v) = true

/-- Every minimal well-formed UTF-8 code unit subsequence has length between
    1 and 4 (inclusive). -/
def spec_well_formed_length_bounds (impl : RepoImpl) : Prop :=
  ∀ (s : List Utf8CodeUnit),
    impl.unicodeV2.utf8IsMinimalWellFormedCodeUnitSubsequence s = true →
    1 ≤ s.length ∧ s.length ≤ 4

/-- When `utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence` returns `some pfx`,
    that pfx is itself a minimal well-formed UTF-8 code unit subsequence. -/
def spec_split_prefix_is_well_formed (impl : RepoImpl) : Prop :=
  ∀ (s : List Utf8CodeUnit) (pfx : List Utf8CodeUnit),
    impl.unicodeV2.utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence s = some pfx →
    impl.unicodeV2.utf8IsMinimalWellFormedCodeUnitSubsequence pfx = true

/-- When `utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence` returns `some pfx`,
    that pfx is a prefix of the original byte sequence. -/
def spec_split_prefix_is_actual_prefix (impl : RepoImpl) : Prop :=
  ∀ (s : List Utf8CodeUnit) (pfx : List Utf8CodeUnit),
    impl.unicodeV2.utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence s = some pfx →
    ∃ rest : List Utf8CodeUnit, s = pfx ++ rest

end Utf8

/-- Scored wrapper for the UTF-8 encode/decode roundtrip helper. -/
def spec_utf8_encode_decode_roundtrip (impl : RepoImpl) : Prop :=
  Utf8.spec_encode_decode_roundtrip impl

/-- Scored wrapper for UTF-8 encoder well-formedness. -/
def spec_utf8_encode_is_well_formed (impl : RepoImpl) : Prop :=
  Utf8.spec_encode_is_well_formed impl

/-- Scored wrapper for UTF-8 split-prefix well-formedness. -/
def spec_utf8_split_prefix_is_well_formed (impl : RepoImpl) : Prop :=
  Utf8.spec_split_prefix_is_well_formed impl

/-- Scored wrapper for UTF-8 split-prefix prefix preservation. -/
def spec_utf8_split_prefix_is_actual_prefix (impl : RepoImpl) : Prop :=
  Utf8.spec_split_prefix_is_actual_prefix impl
