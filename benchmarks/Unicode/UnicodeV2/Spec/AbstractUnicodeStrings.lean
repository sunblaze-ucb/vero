import UnicodeV2.Harness

/-!
# Unicode.Spec.AbstractUnicodeStrings

Specifications for the UTF-8 and UTF-16 encoding/decoding interface.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`;
theorem stubs live in `Unicode/Proof/AbstractUnicodeStrings.lean`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Encoding a string to UTF-8 and then decoding the bytes recovers the original string. -/
def spec_utf8_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (s : String) (bs : List UInt8),
    impl.unicodeV2.absToUTF8Checked s = some bs →
    impl.unicodeV2.absFromUTF8Checked bs = some s

/-- Decoding a valid UTF-8 byte sequence and then re-encoding it recovers the original bytes. -/
def spec_utf8_decode_encode (impl : RepoImpl) : Prop :=
  ∀ (bs : List UInt8) (s : String),
    impl.unicodeV2.absFromUTF8Checked bs = some s →
    impl.unicodeV2.absToUTF8Checked s = some bs

/-- Encoding a string to UTF-16 and then decoding the code units recovers the original string. -/
def spec_utf16_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (s : String) (ws : List UInt16),
    impl.unicodeV2.absToUTF16Checked s = some ws →
    impl.unicodeV2.absFromUTF16Checked ws = some s

/-- Decoding a valid UTF-16 code-unit sequence and then re-encoding it recovers the original units. -/
def spec_utf16_decode_encode (impl : RepoImpl) : Prop :=
  ∀ (ws : List UInt16) (s : String),
    impl.unicodeV2.absFromUTF16Checked ws = some s →
    impl.unicodeV2.absToUTF16Checked s = some ws

/-- The empty string encodes to an empty UTF-8 byte list. -/
def spec_utf8_encode_empty (impl : RepoImpl) : Prop :=
  impl.unicodeV2.absToUTF8Checked "" = some []

/-- An empty UTF-8 byte list decodes to the empty string. -/
def spec_utf8_decode_empty (impl : RepoImpl) : Prop :=
  impl.unicodeV2.absFromUTF8Checked [] = some ""

/-- The empty string encodes to an empty UTF-16 code-unit list. -/
def spec_utf16_encode_empty (impl : RepoImpl) : Prop :=
  impl.unicodeV2.absToUTF16Checked "" = some []

/-- An empty UTF-16 code-unit list decodes to the empty string. -/
def spec_utf16_decode_empty (impl : RepoImpl) : Prop :=
  impl.unicodeV2.absFromUTF16Checked [] = some ""

/-- On source-valid ASCII strings, the specialized ASCII UTF-8 encoder agrees
    with the checked UTF-8 encoder. -/
def spec_asciiToUTF8_matches_checked_on_ascii (impl : RepoImpl) : Prop :=
  ∀ (s : String),
    (∀ c ∈ s.toList, c.val.toNat < 128) →
    impl.unicodeV2.absToUTF8Checked s = some (impl.unicodeV2.absASCIIToUTF8 s)

/-- On source-valid ASCII strings, the specialized ASCII UTF-16 encoder agrees
    with the checked UTF-16 encoder. -/
def spec_asciiToUTF16_matches_checked_on_ascii (impl : RepoImpl) : Prop :=
  ∀ (s : String),
    (∀ c ∈ s.toList, c.val.toNat < 128) →
    impl.unicodeV2.absToUTF16Checked s = some (impl.unicodeV2.absASCIIToUTF16 s)
