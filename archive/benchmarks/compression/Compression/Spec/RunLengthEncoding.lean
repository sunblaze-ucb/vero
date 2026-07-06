import Compression.Harness

/-!
# Compression.Spec.RunLengthEncoding

Specifications for Run-Length Encoding.  Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Strings whose characters cannot be confused with decimal run counts. -/
def spec_rle_helper_noDigitChars (s : String) : Prop :=
  ∀ c : Char, c ∈ s.toList → c.isDigit = false

/-- Encoding the empty string returns the empty string. -/
def spec_rle_encode_empty (impl : RepoImpl) : Prop :=
  impl.compression.run_length_encode "" = ""

/-- Decoding the empty string returns the empty string. -/
def spec_rle_decode_empty (impl : RepoImpl) : Prop :=
  impl.compression.run_length_decode "" = ""

/-- Encoding a single-character string produces "1" followed by that character. -/
def spec_rle_encode_singleton (impl : RepoImpl) : Prop :=
  ∀ c : Char, impl.compression.run_length_encode (String.singleton c) = "1" ++ String.singleton c

/-- Concrete round-trip: decoding the encoding of "AAABBC" recovers "AAABBC". -/
def spec_rle_roundtrip_concrete (impl : RepoImpl) : Prop :=
  impl.compression.run_length_decode (impl.compression.run_length_encode "AAABBC") = "AAABBC"

/-- General round-trip for payloads whose characters are not decimal digits. -/
def spec_rle_roundtrip_nondigit (impl : RepoImpl) : Prop :=
  ∀ s : String,
    spec_rle_helper_noDigitChars s →
    impl.compression.run_length_decode (impl.compression.run_length_encode s) = s

/-- Round-trip on a longer string with multi-digit run counts (12 W's). -/
def spec_rle_roundtrip_long (impl : RepoImpl) : Prop :=
  impl.compression.run_length_decode
      (impl.compression.run_length_encode "WWWWWWWWWWWWBWWWWWWWWWWWWBBB") =
    "WWWWWWWWWWWWBWWWWWWWWWWWWBBB"

/-- Decoding a decimal count followed by one non-digit character repeats that character.
The payload must be a non-digit: the `count ++ char` wire format has no delimiter, so a
digit payload would be swallowed into the count (see `spec_rle_helper_noDigitChars`). -/
def spec_rle_decode_multidigit (impl : RepoImpl) : Prop :=
  ∀ (n : Nat) (c : Char),
    n ≥ 10 →
    c.isDigit = false →
    impl.compression.run_length_decode (toString n ++ String.singleton c) =
      String.ofList (List.replicate n c)
