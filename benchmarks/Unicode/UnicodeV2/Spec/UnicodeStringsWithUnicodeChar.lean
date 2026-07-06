import UnicodeV2.Impl.Unicode
import UnicodeV2.Harness

/-!
# Unicode.Spec.UnicodeStringsWithUnicodeChar

Specifications for the `--unicode-char:true` Unicode string conversion API.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`; theorem stubs
live in `Unicode/Proof/UnicodeStringsWithUnicodeChar.lean`.

In the `--unicode-char:true` mode, Lean `String` values are sequences of valid
Unicode scalar values (surrogates are excluded by the `Char` type). The specs
here capture the invariant that every `Char` is a Unicode scalar value and every
`ScalarValue` is a valid `Char` code point.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Every Lean Char (--unicode-char:true mode) is a valid Unicode scalar value:
    its code point is at most U+10FFFF and is not a surrogate. -/
def spec_char_is_unicode_scalar_value (_impl : RepoImpl) : Prop :=
  ∀ (c : Char),
    let v := c.val.toNat
    v ≤ 0x10FFFF ∧ (v < HIGH_SURROGATE_MIN ∨ v > LOW_SURROGATE_MAX)

/-- Every Unicode ScalarValue corresponds to a valid Lean Char code point:
    its value is either in [0, 0xD7FF] or [0xE000, 0x10FFFF]. -/
def spec_scalar_value_is_char (_impl : RepoImpl) : Prop :=
  ∀ (sv : ScalarValue),
    let v := sv.val.val
    (v < 0xD800 ∨ 0xE000 ≤ v) ∧ v < 0x110000

/-- Helper coverage spec: UTF-8 encoding then decoding recovers the original
    `--unicode-char:true` string. -/
def spec_uniChar_utf8_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (s : String) (bs : List UInt8),
    impl.unicodeV2.uniCharToUTF8Checked s = some bs →
    impl.unicodeV2.uniCharFromUTF8Checked bs = some s

/-- Helper coverage spec: UTF-16 encoding then decoding recovers the original
    `--unicode-char:true` string. -/
def spec_uniChar_utf16_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (s : String) (ws : List UInt16),
    impl.unicodeV2.uniCharToUTF16Checked s = some ws →
    impl.unicodeV2.uniCharFromUTF16Checked ws = some s
