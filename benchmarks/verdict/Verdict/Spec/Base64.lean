import Verdict.Harness

/-!
# Verdict.Spec.Base64

Specifications for Base64 decoding primitives. Each `spec_*` takes
an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- `charToBits` agrees with the base64 alphabet: `'A'..'Z'` → `0..25`. -/
def spec_char_to_bits_upper (impl : RepoImpl) : Prop :=
  ∀ (c : UInt8),
    c ≥ 0x41 → c ≤ 0x5A →
    impl.verdict.charToBits c = some (some (c - 0x41))

/-- `charToBits` agrees with the base64 alphabet: `'a'..'z'` → `26..51`. -/
def spec_char_to_bits_lower (impl : RepoImpl) : Prop :=
  ∀ (c : UInt8),
    c ≥ 0x61 → c ≤ 0x7A →
    impl.verdict.charToBits c = some (some (c - 0x61 + 26))

/-- `charToBits` agrees with the base64 alphabet: `'0'..'9'` → `52..61`. -/
def spec_char_to_bits_digit (impl : RepoImpl) : Prop :=
  ∀ (c : UInt8),
    c ≥ 0x30 → c ≤ 0x39 →
    impl.verdict.charToBits c = some (some (c - 0x30 + 52))

/-- `charToBits '+' = 62`. -/
def spec_char_to_bits_plus (impl : RepoImpl) : Prop :=
  impl.verdict.charToBits 0x2B = some (some 62)

/-- `charToBits '/' = 63`. -/
def spec_char_to_bits_slash (impl : RepoImpl) : Prop :=
  impl.verdict.charToBits 0x2F = some (some 63)

/-- `charToBits` emits `some none` on the padding character `=`. -/
def spec_char_to_bits_padding (impl : RepoImpl) : Prop :=
  impl.verdict.charToBits 0x3D = some none

/-- `charToBits` rejects any character outside the Base64 alphabet. -/
def spec_char_to_bits_reject (impl : RepoImpl) : Prop :=
  ∀ (c : UInt8),
    (c < 0x2B ∨ (c > 0x2B ∧ c < 0x2F) ∨
     (c > 0x39 ∧ c < 0x3D) ∨ (c > 0x3D ∧ c < 0x41) ∨
     (c > 0x5A ∧ c < 0x61) ∨ c > 0x7A) →
    impl.verdict.charToBits c = none

/-- `decode6Bits` always produces exactly 3 bytes. -/
def spec_decode_6_bits_length (impl : RepoImpl) : Prop :=
  ∀ (a b c d : UInt8), (impl.verdict.decode6Bits a b c d).length = 3

/-- Bit layout of byte 0: top 6 bits of `a`, low 2 from top of `b`. -/
def spec_decode_6_bits_byte0 (impl : RepoImpl) : Prop :=
  ∀ (a b c d : UInt8),
    (impl.verdict.decode6Bits a b c d)[0]? = some ((a <<< 2) ||| (b >>> 4))

/-- Bit layout of byte 1: low 4 of `b`, high 4 from top of `c`. -/
def spec_decode_6_bits_byte1 (impl : RepoImpl) : Prop :=
  ∀ (a b c d : UInt8),
    (impl.verdict.decode6Bits a b c d)[1]? = some ((b <<< 4) ||| (c >>> 2))

/-- Bit layout of byte 2: low 2 of `c` plus all of `d`. -/
def spec_decode_6_bits_byte2 (impl : RepoImpl) : Prop :=
  ∀ (a b c d : UInt8),
    (impl.verdict.decode6Bits a b c d)[2]? = some ((c <<< 6) ||| d)

/-- `decodeBase64` on a 4-byte well-formed block (no padding) produces
    3 bytes of output. -/
def spec_decode_base64_length (impl : RepoImpl) : Prop :=
  ∀ (input : Verdict.Bytes) (output : Verdict.Bytes),
    impl.verdict.decodeBase64 input = some output →
    input.length % 4 = 0 →
    output.length * 4 = input.length * 3

/-- `parseX509Base64` succeeds only when `decodeBase64` does. -/
def spec_parse_x509_base64_pipeline (impl : RepoImpl) : Prop :=
  ∀ (input : Verdict.Bytes),
    impl.verdict.parseX509Base64 input =
      (impl.verdict.decodeBase64 input >>= Verdict.parseX509Der)

/-- Empty input decodes to empty output. Dafny… Verus: base case of
    `spec_parse_helper` in `verdict-parser/src/common/base64.rs`. -/
def spec_decode_base64_empty (impl : RepoImpl) : Prop :=
  impl.verdict.decodeBase64 [] = some []

/-- Successful decoding requires a length that's a multiple of 4 — in
    the benchmark's no-padding variant, any residual input after
    consuming 4-byte blocks causes rejection. Mirrors Verus
    `spec_parse_helper` only succeeding on 4-byte-aligned input. -/
def spec_decode_base64_requires_multiple_of_4 (impl : RepoImpl) : Prop :=
  ∀ (input output : Verdict.Bytes),
    impl.verdict.decodeBase64 input = some output →
    input.length % 4 = 0

/-- When `charToBits` returns a valid 6-bit value, it's in the range
    `0..63`. Follows from the exhaustive case analysis in
    `spec_char_to_bits`, which maps each Base64-alphabet byte to a
    fixed 6-bit codeword. -/
def spec_char_to_bits_value_bound (impl : RepoImpl) : Prop :=
  ∀ (c : UInt8) (v : UInt8),
    impl.verdict.charToBits c = some (some v) →
    v ≤ 63
