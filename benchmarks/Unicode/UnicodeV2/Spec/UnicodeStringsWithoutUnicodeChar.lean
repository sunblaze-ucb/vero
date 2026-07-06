import UnicodeV2.Harness

/-!
# Unicode.Spec.UnicodeStringsWithoutUnicodeChar

Specifications for the `--unicode-char:false` Unicode string conversion API.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`; theorem stubs
live in `Unicode/Proof/UnicodeStringsWithoutUnicodeChar.lean`.

In the `--unicode-char:false` model a Dafny string is represented as a raw
`List UInt16` (UTF-16 code units that may or may not form a valid Unicode
sequence). The four entry points operate on this representation rather than
on Lean `String` values.

DO NOT MODIFY — this file is frozen curator-given content.
-/

namespace Unicode

/-- True iff the sequence of UTF-16 code units is well-formed: every
    non-surrogate code unit is a standalone BMP character, and every
    high surrogate (U+D800–U+DBFF) is immediately followed by a low
    surrogate (U+DC00–U+DFFF). -/
def isWellFormedString (s : List UInt16) : Bool :=
  let rec go : List UInt16 → Bool
    | [] => true
    | c :: rest =>
      if decide (HIGH_SURROGATE_MIN ≤ c.toNat ∧ c.toNat ≤ HIGH_SURROGATE_MAX) then
        match rest with
        | d :: rest' => decide (LOW_SURROGATE_MIN ≤ d.toNat ∧ d.toNat ≤ LOW_SURROGATE_MAX) && go rest'
        | [] => false
      else if decide (LOW_SURROGATE_MIN ≤ c.toNat ∧ c.toNat ≤ LOW_SURROGATE_MAX) then false
      else go rest
  go s

end Unicode

/-- Converting a raw UTF-16 sequence to UTF-8 and back returns the original sequence. -/
def spec_noChar_utf8_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (s : List UInt16) (bs : List UInt8),
    impl.unicodeV2.noCharToUTF8Checked s = some bs →
    impl.unicodeV2.noCharFromUTF8Checked bs = some s

/-- Decoding a UTF-8 byte sequence and re-encoding to UTF-16 recovers the original bytes. -/
def spec_noChar_utf8_decode_encode (impl : RepoImpl) : Prop :=
  ∀ (bs : List UInt8) (s : List UInt16),
    impl.unicodeV2.noCharFromUTF8Checked bs = some s →
    impl.unicodeV2.noCharToUTF8Checked s = some bs

/-- `noCharToUTF16Checked` returns the input sequence unchanged when it succeeds. -/
def spec_noCharToUTF16_returns_input (impl : RepoImpl) : Prop :=
  ∀ (s : List UInt16) (t : List UInt16),
    impl.unicodeV2.noCharToUTF16Checked s = some t →
    t = s

/-- `noCharFromUTF16Checked` returns the input sequence unchanged when it succeeds. -/
def spec_noCharFromUTF16_returns_input (impl : RepoImpl) : Prop :=
  ∀ (bs : List UInt16) (t : List UInt16),
    impl.unicodeV2.noCharFromUTF16Checked bs = some t →
    t = bs

/-- `noCharToUTF16Checked` and `noCharFromUTF16Checked` agree: one succeeds iff the other does. -/
def spec_noCharToUTF16_iff_noCharFromUTF16 (impl : RepoImpl) : Prop :=
  ∀ (s : List UInt16),
    (impl.unicodeV2.noCharToUTF16Checked s).isSome =
    (impl.unicodeV2.noCharFromUTF16Checked s).isSome

/-- Encoding an empty UTF-16 sequence to UTF-8 yields an empty byte list. -/
def spec_noCharToUTF8_empty (impl : RepoImpl) : Prop :=
  impl.unicodeV2.noCharToUTF8Checked [] = some []

/-- Decoding an empty UTF-8 byte list yields an empty UTF-16 sequence. -/
def spec_noCharFromUTF8_empty (impl : RepoImpl) : Prop :=
  impl.unicodeV2.noCharFromUTF8Checked [] = some []

/-- Validating an empty sequence as UTF-16 succeeds and returns the empty sequence. -/
def spec_noCharToUTF16_empty (impl : RepoImpl) : Prop :=
  impl.unicodeV2.noCharToUTF16Checked [] = some []

/-- Validating an empty `uint16` sequence as UTF-16 succeeds and returns the empty sequence. -/
def spec_noCharFromUTF16_empty (impl : RepoImpl) : Prop :=
  impl.unicodeV2.noCharFromUTF16Checked [] = some []

/-- `noCharToUTF8Checked` returns `none` exactly when the input is not well-formed UTF-16. -/
def spec_noCharToUTF8_none_iff_malformed (impl : RepoImpl) : Prop :=
  ∀ (s : List UInt16),
    impl.unicodeV2.noCharToUTF8Checked s = none ↔
    impl.unicodeV2.noCharToUTF16Checked s = none

/-- `noCharFromUTF16Checked` succeeds iff `noCharToUTF16Checked` succeeds on the same input. -/
def spec_noCharFromUTF16_iff_toUTF16 (impl : RepoImpl) : Prop :=
  ∀ (bs : List UInt16),
    impl.unicodeV2.noCharFromUTF16Checked bs = impl.unicodeV2.noCharToUTF16Checked bs
