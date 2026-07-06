import UnicodeV2.Harness

/-!
# Unicode.Spec.Utf16EncodingForm

Specifications for the UTF-16 encoding form operations. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; theorem stubs live in
`Unicode/Proof/Utf16EncodingForm.lean`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

namespace Utf16

/-- Encoding a scalar value and then decoding the result returns the original scalar value. -/
def spec_encode_decode_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (v : ScalarValue),
    impl.unicodeV2.utf16DecodeMinimalWellFormedCodeUnitSubsequence
      (impl.unicodeV2.utf16EncodeScalarValue v) = v

/-- Encoding a scalar value always produces a minimal well-formed code unit subsequence. -/
def spec_encode_is_minimal_well_formed (impl : RepoImpl) : Prop :=
  ∀ (v : ScalarValue),
    impl.unicodeV2.utf16IsMinimalWellFormedCodeUnitSubsequence
      (impl.unicodeV2.utf16EncodeScalarValue v) = true

/-- Splitting a pfx from an empty sequence always returns none. -/
def spec_split_prefix_empty_is_none (impl : RepoImpl) : Prop :=
  impl.unicodeV2.utf16SplitPrefixMinimalWellFormedCodeUnitSubsequence [] = none

/-- If split-prefix returns `some pfx`, then `pfx` is a minimal well-formed subsequence. -/
def spec_split_prefix_some_is_well_formed (impl : RepoImpl) : Prop :=
  ∀ (s : List Utf16CodeUnit) (pfx : List Utf16CodeUnit),
    impl.unicodeV2.utf16SplitPrefixMinimalWellFormedCodeUnitSubsequence s = some pfx →
    impl.unicodeV2.utf16IsMinimalWellFormedCodeUnitSubsequence pfx = true

/-- If split-prefix returns `some pfx`, then `pfx` is the leading segment of `s`. -/
def spec_split_prefix_is_actual_prefix (impl : RepoImpl) : Prop :=
  ∀ (s : List Utf16CodeUnit) (pfx : List Utf16CodeUnit),
    impl.unicodeV2.utf16SplitPrefixMinimalWellFormedCodeUnitSubsequence s = some pfx →
    s.take pfx.length = pfx

/-- A single-element sequence is minimal well-formed iff the code unit is a BMP scalar value
    (i.e., not in the surrogate range U+D800–U+DFFF). -/
def spec_is_minimal_single_bmp (impl : RepoImpl) : Prop :=
  ∀ (w : Utf16CodeUnit),
    impl.unicodeV2.utf16IsMinimalWellFormedCodeUnitSubsequence [w] = true ↔
    (w.toNat ≤ 0xD7FF ∨ 0xE000 ≤ w.toNat)

/-- A two-element sequence is minimal well-formed iff it is a valid surrogate pair:
    a high surrogate (U+D800–U+DBFF) followed by a low surrogate (U+DC00–U+DFFF). -/
def spec_is_minimal_surrogate_pair (impl : RepoImpl) : Prop :=
  ∀ (w1 w2 : Utf16CodeUnit),
    impl.unicodeV2.utf16IsMinimalWellFormedCodeUnitSubsequence [w1, w2] = true ↔
    (HIGH_SURROGATE_MIN ≤ w1.toNat ∧ w1.toNat ≤ HIGH_SURROGATE_MAX ∧
     LOW_SURROGATE_MIN  ≤ w2.toNat ∧ w2.toNat ≤ LOW_SURROGATE_MAX)

end Utf16

/-- Scored wrapper for the UTF-16 encode/decode roundtrip helper. -/
def spec_utf16_encode_decode_roundtrip (impl : RepoImpl) : Prop :=
  Utf16.spec_encode_decode_roundtrip impl

/-- Scored wrapper for UTF-16 encoder minimal well-formedness. -/
def spec_utf16_encode_is_minimal_well_formed (impl : RepoImpl) : Prop :=
  Utf16.spec_encode_is_minimal_well_formed impl

/-- Scored wrapper for the empty UTF-16 split-prefix behavior. -/
def spec_utf16_split_prefix_empty_is_none (impl : RepoImpl) : Prop :=
  Utf16.spec_split_prefix_empty_is_none impl

/-- Scored wrapper for UTF-16 split-prefix well-formedness. -/
def spec_utf16_split_prefix_some_is_well_formed (impl : RepoImpl) : Prop :=
  Utf16.spec_split_prefix_some_is_well_formed impl

/-- Scored wrapper for UTF-16 split-prefix prefix preservation. -/
def spec_utf16_split_prefix_is_actual_prefix (impl : RepoImpl) : Prop :=
  Utf16.spec_split_prefix_is_actual_prefix impl
