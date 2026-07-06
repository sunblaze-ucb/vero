import Base58.Harness

/-!
# Base58.Spec.Codec

Specifications for the base58 codec. Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`; an API is always reached through
`impl.base58.<fn>`, never by calling the reference `Base58.<fn>` directly.

The frozen ground-truth machinery below (`b58Idx`/`positionalValue`/
`isCanonicalNumeral`/`leadingOnes`/`beValueGT`/…) never refers to `impl`, so it
fixes the radix, the alphabet, and what "canonical" means independently of any
implementation.

DO NOT MODIFY — this file is frozen curator-given content.
-/

namespace Base58Spec

-- ── Frozen ground-truth machinery (DO NOT MODIFY) ────────────────

/-- The frozen positional-value oracle: the base58 value of a character list,
    `Σ idx(cᵢ) · 58^(k-1-i)`; `none` if any character is outside the alphabet.
    Ground truth for the spec; never refers to any implementation. -/
def positionalValue (cs : List Char) : Option Nat :=
  cs.foldl
    (fun acc c =>
      match acc, b58Idx c with
      | some n, some d => some (n * 58 + d)
      | _, _ => none)
    (some 0)

/-- Every character of `s` is a frozen-alphabet character. -/
def allValid (s : String) : Bool := s.toList.all (fun c => (b58Idx c).isSome)

/-- The frozen canonicality predicate for an integer numeral. A canonical
    base58 numeral is nonempty, uses only frozen-alphabet characters, and has no
    redundant leading `'1'` (the zero digit) — *unless* it is the single-digit
    zero numeral `"1"` itself. Thus exactly one numeral represents each value:
    `"1"` for `0`, and for `n > 0` the leading digit is nonzero. -/
def isCanonicalNumeral (s : String) : Bool :=
  match s.toList with
  | [] => false
  | [c] => (b58Idx c).isSome
  | c :: _ => (b58Idx c).isSome && c != '1' && allValid s

/-- Count of leading `'1'` characters (the zero-digit prefix). -/
def leadingOnes : List Char → Nat
  | [] => 0
  | c :: rest => if c == '1' then leadingOnes rest + 1 else 0

/-- Count of leading zero bytes in a byte string. -/
def leadingZeroBytesGT : Bytes → Nat
  | [] => 0
  | b :: rest => if b == 0 then leadingZeroBytesGT rest + 1 else 0

/-- The significant suffix after dropping leading zero bytes. -/
def dropLeadingZeroBytesGT : Bytes → Bytes
  | [] => []
  | b :: rest => if b == 0 then dropLeadingZeroBytesGT rest else b :: rest

/-- The frozen big-endian integer value of a byte string (`Σ bᵢ · 256^k`). -/
def beValueGT (bytes : Bytes) : Nat := bytes.foldl (fun acc b => acc * 256 + b) 0

/-- The frozen digit value of a base58 character (its alphabet index; `0` off-alphabet). -/
def digitValueGT (c : Char) : Nat := (b58Idx c).getD 0

/-- The frozen explicit place-value sum of a base58 numeral: `Σᵢ idx(cᵢ)·58^(k-1-i)`
    over positions `i` of a `k`-character list, computed via `List.range`. -/
def base58PlaceValueSum (cs : List Char) : Nat :=
  (List.range cs.length).foldl
    (fun acc i => acc + digitValueGT (cs.getD i '1') * 58 ^ (cs.length - 1 - i))
    0

/-- The frozen most-significant-first base-58 digit-value expansion of `n`
    (repeated div/mod by 58), with `0` expanding to `[0]`. -/
def base58DigitValuesAux : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | _, 0, acc => acc
  | fuel + 1, n, acc => base58DigitValuesAux fuel (n / 58) (n % 58 :: acc)

/-- The frozen base-58 digit-value list of `n` (`[0]` for `0`). -/
def base58DigitValues (n : Nat) : List Nat :=
  if n == 0 then [0] else base58DigitValuesAux n n []

/-- The frozen sorted support of a digit-value list: the digit values `0…57`
    that occur at least once, in ascending order. -/
def digitSupportValues (ds : List Nat) : List Nat :=
  (List.range 58).filter (fun d => decide (0 < ds.count d))

/-- The frozen sorted support of a numeral's characters: the frozen-alphabet
    characters that occur at least once, in alphabet order. -/
def encodedSupportChars (s : String) : List Char :=
  b58Alphabet.filter (fun c => decide (0 < s.toList.count c))

/-- The frozen least-significant (last) character of a character list; `'1'` for
    the empty list. -/
def base58LastCharGT (cs : List Char) : Char :=
  match cs.reverse with
  | [] => '1'
  | c :: _ => c

/-- The frozen prefix of a character list with its last character removed. -/
def base58DropLastCharGT : List Char → List Char
  | [] => []
  | _ :: [] => []
  | c :: rest => c :: base58DropLastCharGT rest

/-- The frozen big-endian base-256 byte expansion of `n` (repeated div/mod by
    256, most-significant first); `fuel` bounds the recursion. -/
def toBytesGTAux : Nat → Nat → Bytes → Bytes
  | 0, _, acc => acc
  | _, 0, acc => acc
  | fuel + 1, n, acc => toBytesGTAux fuel (n / 256) ((n % 256) :: acc)

/-- The frozen big-endian byte expansion of a `Nat` (`0` expands to `[]`). -/
def toBytesGT (n : Nat) : Bytes := if n == 0 then [] else toBytesGTAux n n []

/-- The frozen significant base58 suffix of `s`: the string after its leading
    `'1'`s are dropped. -/
def significantBase58SuffixGT (s : String) : String :=
  String.ofList (s.toList.dropWhile (· == '1'))

/-- The frozen canonical-byte-encoding predicate: `s` is a canonical byte
    encoding iff its significant suffix is either empty (all-`'1'` string) or a
    canonical numeral. -/
def isCanonicalByteEncodingGT (s : String) : Bool :=
  let rest := significantBase58SuffixGT s
  match rest.toList with
  | [] => true
  | _ => isCanonicalNumeral rest

-- ════════════════════════════════════════════════════════════════
-- decodeInt: the positional-value oracle and its laws.
-- ════════════════════════════════════════════════════════════════

/-- Positional value: `decodeInt s` equals the frozen positional value of `s`
    over the frozen alphabet — `Σ idx(cᵢ) · 58^(k-1-i)`. Exactly one correct
    value for each string. -/
def spec_decode_int_positional_value (impl : RepoImpl) : Prop :=
  ∀ s : String, impl.base58.decodeInt s = positionalValue s.toList

/-- The empty numeral decodes to `some 0`. -/
def spec_decode_int_empty (impl : RepoImpl) : Prop :=
  impl.base58.decodeInt "" = some 0

/-- Invalid-character rejection: if any character of `s` is outside the frozen
    alphabet, `decodeInt s = none`. -/
def spec_decode_int_invalid_char (impl : RepoImpl) : Prop :=
  ∀ s : String, allValid s = false → impl.base58.decodeInt s = none

/-- Horner step: appending a single character `c` to a valid numeral `s`
    multiplies the running value by `58` and adds the digit `idx c` —
    `decodeInt (s ++ singleton c) = decodeInt s * 58 + idx c`. -/
def spec_decode_int_horner_step (impl : RepoImpl) : Prop :=
  ∀ (s : String) (c : Char) (n d : Nat),
    impl.base58.decodeInt s = some n → b58Idx c = some d →
      impl.base58.decodeInt (s ++ String.singleton c) = some (n * 58 + d)

-- ════════════════════════════════════════════════════════════════
-- encodeInt: value-agreement and canonicality.
-- ════════════════════════════════════════════════════════════════

/-- Value-agreement: the numeral `encodeInt n` decodes back to `n`. -/
def spec_encode_int_value_agreement (impl : RepoImpl) : Prop :=
  ∀ n : Nat, impl.base58.decodeInt (impl.base58.encodeInt n) = some n

/-- Canonicality: `encodeInt n` is always a canonical numeral — nonempty,
    all-valid, and with no redundant leading `'1'` zero digit beyond the genuine
    zero `"1"`. -/
def spec_encode_int_canonical (impl : RepoImpl) : Prop :=
  ∀ n : Nat, isCanonicalNumeral (impl.base58.encodeInt n) = true

/-- Uniqueness: any canonical numeral with value `n` *is* `encodeInt n` — if
    `decodeInt s = some n` and `s` is canonical, then `s = encodeInt n`. -/
def spec_encode_int_unique (impl : RepoImpl) : Prop :=
  ∀ (s : String) (n : Nat),
    impl.base58.decodeInt s = some n → isCanonicalNumeral s = true →
      s = impl.base58.encodeInt n

/-- The canonical numeral for `0` is the single zero digit `"1"`. -/
def spec_encode_int_zero (impl : RepoImpl) : Prop :=
  impl.base58.encodeInt 0 = "1"

/-- No redundant leading zero digit for positives: for `n > 0`, `encodeInt n`
    does not begin with `'1'`. -/
def spec_encode_int_no_leading_zero_digit (impl : RepoImpl) : Prop :=
  ∀ n : Nat, n > 0 → (impl.base58.encodeInt n).toList.head? ≠ some '1'

-- ════════════════════════════════════════════════════════════════
-- encode (bytes): the leading-zero boundary.
-- ════════════════════════════════════════════════════════════════

/-- Leading-zero boundary: a byte string of `z` leading zero bytes followed by a
    nonempty significant suffix `rest` (first byte nonzero) encodes to `z`
    literal `'1'`s followed by the `encodeInt` of the suffix's big-endian
    value. -/
def spec_encode_leading_zero_boundary (impl : RepoImpl) : Prop :=
  ∀ (z : Nat) (b : Nat) (rest : Bytes), b ≠ 0 →
    impl.base58.encode (List.replicate z 0 ++ (b :: rest))
      = String.ofList (List.replicate z '1') ++ impl.base58.encodeInt (beValueGT (b :: rest))

/-- All-zeros: a byte string of `z` zero bytes encodes to exactly `z` `'1'`s. -/
def spec_encode_all_zeros (impl : RepoImpl) : Prop :=
  ∀ z : Nat, impl.base58.encode (List.replicate z 0) = String.ofList (List.replicate z '1')

/-- The empty byte string encodes to the empty string. -/
def spec_encode_empty (impl : RepoImpl) : Prop :=
  impl.base58.encode [] = ""

/-- Leading-`'1'` count law: the number of leading `'1'`s in `encode bytes`
    equals the number of leading zero bytes in `bytes`, for every byte string. -/
def spec_encode_leading_one_count (impl : RepoImpl) : Prop :=
  ∀ bytes : Bytes,
    leadingOnes (impl.base58.encode bytes).toList = leadingZeroBytesGT bytes

-- ════════════════════════════════════════════════════════════════
-- decode (bytes): inverse laws and rejection.
-- ════════════════════════════════════════════════════════════════

/-- Decode rejects an invalid character: if the portion of `s` after its leading
    `'1'`s contains a character outside the frozen alphabet, `decode s = none`. -/
def spec_decode_invalid_char (impl : RepoImpl) : Prop :=
  ∀ s : String,
    allValid (String.ofList (s.toList.dropWhile (· == '1'))) = false →
      impl.base58.decode s = none

/-- Decode of all-`'1'`s: a string of `z` `'1'`s decodes to `z` zero bytes. -/
def spec_decode_all_ones (impl : RepoImpl) : Prop :=
  ∀ z : Nat, impl.base58.decode (String.ofList (List.replicate z '1')) = some (List.replicate z 0)

-- ════════════════════════════════════════════════════════════════
-- Concrete frozen-vector anchors.
--
-- Golden base58 values of known small inputs, pinning the frozen alphabet
-- ordering and the radix concretely.
-- ════════════════════════════════════════════════════════════════

/-- Concrete `encodeInt` vectors over the frozen alphabet: `0 ↦ "1"`,
    `1 ↦ "2"`, `57 ↦ "z"`, `58 ↦ "21"`, `256 ↦ "5R"`, `1000 ↦ "JF"`. Pins the
    frozen alphabet ordering and the radix on golden values. -/
def spec_vector_encode_int (impl : RepoImpl) : Prop :=
  impl.base58.encodeInt 0 = "1" ∧
  impl.base58.encodeInt 1 = "2" ∧
  impl.base58.encodeInt 57 = "z" ∧
  impl.base58.encodeInt 58 = "21" ∧
  impl.base58.encodeInt 256 = "5R" ∧
  impl.base58.encodeInt 1000 = "JF"

/-- Concrete `decodeInt` vectors over the frozen alphabet: the same golden pairs
    in the decode direction, plus the empty string. Pins the alphabet ordering
    and place value concretely. -/
def spec_vector_decode_int (impl : RepoImpl) : Prop :=
  impl.base58.decodeInt "1" = some 0 ∧
  impl.base58.decodeInt "z" = some 57 ∧
  impl.base58.decodeInt "21" = some 58 ∧
  impl.base58.decodeInt "5R" = some 256 ∧
  impl.base58.decodeInt "JF" = some 1000

/-- Concrete `encode`/`decode` byte vectors: leading-zero bytes (`[0,0,1] ↦
    "112"`), a single significant byte (`[255] ↦ "5Q"`), and a mixed case
    (`[0,255] ↦ "15Q"`), with the decode direction agreeing. Pins the full byte
    boundary convention on golden vectors. -/
def spec_vector_encode_bytes (impl : RepoImpl) : Prop :=
  impl.base58.encode [0, 0, 1] = "112" ∧
  impl.base58.encode [255] = "5Q" ∧
  impl.base58.encode [0, 255] = "15Q" ∧
  impl.base58.decode "112" = some [0, 0, 1] ∧
  impl.base58.decode "5Q" = some [255]

-- ════════════════════════════════════════════════════════════════
-- Deep round-trip and radix-magnitude laws.
--
-- Each states a clean end fact (a round-trip identity, an injectivity, a
-- numeral-length value, or a value bound) that holds over all inputs.
-- ════════════════════════════════════════════════════════════════

/-- Full byte round-trip: for *every* byte string whose bytes are in range
    (`< 256`), including arbitrarily many leading zero bytes, decoding the
    encoding recovers the original bytes exactly — `decode (encode bytes) =
    some bytes`. -/
def spec_roundtrip_bytes (impl : RepoImpl) : Prop :=
  ∀ bytes : Bytes, (∀ b ∈ bytes, b < 256) →
    impl.base58.decode (impl.base58.encode bytes) = some bytes

/-- `decodeInt` injectivity on canonical numerals: two canonical numerals with
    the same positional value are the *same* numeral — `decodeInt s = decodeInt t
    = some n` with both `s`, `t` canonical forces `s = t`. -/
def spec_decode_int_injective (impl : RepoImpl) : Prop :=
  ∀ (s t : String) (n : Nat),
    isCanonicalNumeral s = true → isCanonicalNumeral t = true →
    impl.base58.decodeInt s = some n → impl.base58.decodeInt t = some n →
      s = t

/-- `encodeInt` length band: for `n` in the band `[58^(k-1), 58^k)` (with
    `k ≥ 1`), the canonical numeral `encodeInt n` has exactly `k` digits. -/
def spec_encode_int_length_band (impl : RepoImpl) : Prop :=
  ∀ (n k : Nat), 1 ≤ k → 58 ^ (k - 1) ≤ n → n < 58 ^ k →
    (impl.base58.encodeInt n).length = k

/-- `decodeInt` value magnitude bound: a numeral of length `k` decodes to a value
    strictly below `58^k` — `decodeInt s = some n` implies `n < 58 ^ s.length`. -/
def spec_decode_int_value_lt (impl : RepoImpl) : Prop :=
  ∀ (s : String) (n : Nat), impl.base58.decodeInt s = some n → n < 58 ^ s.length

/-- Leading-zero count preserved through the byte round-trip: when
    `decode (encode bytes) = some out` for an in-range byte string, the decoded
    `out` has the same leading-zero-byte count as `bytes`. -/
def spec_leading_zero_preservation (impl : RepoImpl) : Prop :=
  ∀ (bytes out : Bytes), (∀ b ∈ bytes, b < 256) →
    impl.base58.decode (impl.base58.encode bytes) = some out →
      leadingZeroBytesGT out = leadingZeroBytesGT bytes

/-- Numeral round-trip on the canonical domain: for a canonical numeral `s` of
    value `n`, re-encoding that value reproduces `s` exactly — `decodeInt s =
    some n` and `s` canonical imply `encodeInt n = s`. -/
def spec_numeral_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (s : String) (n : Nat),
    isCanonicalNumeral s = true → impl.base58.decodeInt s = some n →
      impl.base58.encodeInt n = s

-- ════════════════════════════════════════════════════════════════
-- Positional place-value, digit-multiset, and most-significant-digit laws.
--
-- Each states a clean end fact over all inputs, phrased against an explicit
-- ground-truth quantity (place-value sum, digit-value multiset, support) that
-- is only propositionally — not definitionally — equal to the impl's fold.
-- ════════════════════════════════════════════════════════════════

/-- Place-value evaluation: for a valid numeral `s`, `decodeInt s` equals its
    explicit positional place-value sum `Σᵢ idx(cᵢ)·58^(k-1-i)`. -/
def spec_decode_int_place_value_sum (impl : RepoImpl) : Prop :=
  ∀ s : String, allValid s = true →
    impl.base58.decodeInt s = some (base58PlaceValueSum s.toList)

/-- Digit occurrence law: for every digit value `d < 58`, the number of times the
    character `b58Char d` occurs in `encodeInt n` equals the number of times `d`
    occurs in the ground-truth base-58 digit-value expansion of `n`. -/
def spec_encode_int_digit_count_values (impl : RepoImpl) : Prop :=
  ∀ (n d : Nat), d < 58 →
    (impl.base58.encodeInt n).toList.count (b58Char d) =
      (base58DigitValues n).count d

/-- Support agreement: the digit values of the distinct characters occurring in
    `encodeInt n` (in alphabet order) equal the distinct digit values occurring
    in the ground-truth base-58 expansion of `n` (in ascending order). -/
def spec_encode_int_support_values (impl : RepoImpl) : Prop :=
  ∀ n : Nat,
    (encodedSupportChars (impl.base58.encodeInt n)).map digitValueGT =
      digitSupportValues (base58DigitValues n)

/-- Most-significant digit: for `n > 0`, the digit value of the first character
    of `encodeInt n` equals `n / 58^(len-1)` — the most-significant base-58
    digit of `n`. -/
def spec_encode_int_msd_quotient (impl : RepoImpl) : Prop :=
  ∀ n : Nat, n > 0 →
    b58Idx ((impl.base58.encodeInt n).toList.getD 0 '1') =
      some (n / 58 ^ ((impl.base58.encodeInt n).length - 1))

-- ════════════════════════════════════════════════════════════════
-- Full positional digit laws, byte-boundary decomposition, and exact
-- magnitude bands.
--
-- Each states a clean end fact — a per-position digit value, a
-- most-/least-significant decomposition, a byte-decode decomposition, an
-- injectivity, or an exact length band — over all inputs, phrased against
-- frozen ground-truth quantities.
-- ════════════════════════════════════════════════════════════════

/-- Per-position digit: the digit value at position `i` of `encodeInt n` is the
    quotient-by-place-value digit `(n / 58^(len-1-i)) % 58`, for every in-range
    position `i`. -/
def spec_encode_int_digit_at_place_quot_mod (impl : RepoImpl) : Prop :=
  ∀ (n i : Nat), i < (impl.base58.encodeInt n).toList.length →
    b58Idx ((impl.base58.encodeInt n).toList.getD i '1') =
      some ((n / (58 ^ ((impl.base58.encodeInt n).toList.length - 1 - i))) % 58)

/-- Most-significant-digit decomposition: for `n > 0`, `encodeInt n` splits as a
    head digit `d` and tail, with `n = d · 58^(tail.length) + decodeInt tail`
    and the tail value strictly below `58^(tail.length)`. -/
def spec_encode_int_msd_tail_decomposition (impl : RepoImpl) : Prop :=
  ∀ n : Nat, n > 0 →
    match (impl.base58.encodeInt n).toList with
    | [] => False
    | c :: tail =>
        match b58Idx c, impl.base58.decodeInt (String.ofList tail) with
        | some d, some tailVal =>
            n = d * 58 ^ tail.length + tailVal ∧ tailVal < 58 ^ tail.length
        | _, _ => False

/-- Least-significant-digit split: for `n > 0`, dropping the last character of
    `encodeInt n` decodes to `n / 58`, and that last character's digit value is
    `n % 58`. -/
def spec_encode_int_last_digit_divmod (impl : RepoImpl) : Prop :=
  ∀ n : Nat, n > 0 →
    impl.base58.decodeInt
        (String.ofList (base58DropLastCharGT ((impl.base58.encodeInt n).toList)))
      = some (n / 58) ∧
    b58Idx (base58LastCharGT ((impl.base58.encodeInt n).toList)) = some (n % 58)

/-- Self place-value: the explicit positional place-value sum of `encodeInt n`
    is exactly `n`, for every `n`. -/
def spec_encode_int_place_value_self (impl : RepoImpl) : Prop :=
  ∀ n : Nat, base58PlaceValueSum ((impl.base58.encodeInt n).toList) = n

/-- Exact length band: the length `k` of `encodeInt n` is the exact base58
    magnitude band of `n` — either `k = 1` with `n < 58`, or `k > 1` with
    `58^(k-1) ≤ n < 58^k`. -/
def spec_encode_int_length_exact_bounds (impl : RepoImpl) : Prop :=
  ∀ n : Nat,
    let k := (impl.base58.encodeInt n).toList.length
    (k = 1 ∧ n < 58) ∨ (1 < k ∧ 58 ^ (k - 1) ≤ n ∧ n < 58 ^ k)

/-- Digit-insertion contribution: inserting a valid digit `c` between a prefix
    `pre` (value `p`) and suffix `post` (value `s`) yields the value
    `p·58^(post.length+1) + idx(c)·58^(post.length) + s`. -/
def spec_decode_int_split_digit_contribution (impl : RepoImpl) : Prop :=
  ∀ (pre post : List Char) (c : Char) (p s d : Nat),
    impl.base58.decodeInt (String.ofList pre) = some p →
    impl.base58.decodeInt (String.ofList post) = some s →
    b58Idx c = some d →
      impl.base58.decodeInt (String.ofList (pre ++ (c :: post))) =
        some (p * 58 ^ (post.length + 1) + d * 58 ^ post.length + s)

/-- Canonical value band: a canonical numeral `s` of length `k` and value `n`
    satisfies the exact magnitude band — either `k = 1` with `n < 58`, or
    `k > 1` with `58^(k-1) ≤ n < 58^k`. -/
def spec_decode_int_canonical_value_band (impl : RepoImpl) : Prop :=
  ∀ (s : String) (n : Nat),
    isCanonicalNumeral s = true →
    impl.base58.decodeInt s = some n →
      let k := s.toList.length
      (k = 1 ∧ n < 58) ∨ (1 < k ∧ 58 ^ (k - 1) ≤ n ∧ n < 58 ^ k)

/-- Byte-decode decomposition: when the significant suffix of `s` decodes to
    value `v`, `decode s` is `leadingOnes s` zero bytes followed by the frozen
    big-endian byte expansion of `v`. -/
def spec_decode_value_bytes_decomposition (impl : RepoImpl) : Prop :=
  ∀ (s : String) (v : Nat),
    impl.base58.decodeInt (significantBase58SuffixGT s) = some v →
      impl.base58.decode s =
        some (List.replicate (leadingOnes s.toList) 0 ++ toBytesGT v)

/-- Significant-suffix value: the base58 numeral remaining after the encoded
    leading-zero `'1'` prefix of `encode bytes` decodes to the big-endian value
    of `bytes`' significant (leading-zero-stripped) suffix. -/
def spec_encode_significant_suffix_value (impl : RepoImpl) : Prop :=
  ∀ bytes : Bytes,
    impl.base58.decodeInt
      (String.ofList
        (List.drop (leadingZeroBytesGT bytes) (impl.base58.encode bytes).toList)) =
      some (beValueGT (dropLeadingZeroBytesGT bytes))

/-- Positive payload decode: for `n > 0`, `z` leading `'1'`s followed by
    `encodeInt n` decodes to `z` zero bytes followed by the frozen byte
    expansion of `n`. -/
def spec_decode_positive_integer_payload (impl : RepoImpl) : Prop :=
  ∀ (z n : Nat), n > 0 →
    impl.base58.decode
      (String.ofList (List.replicate z '1') ++ impl.base58.encodeInt n) =
      some (List.replicate z 0 ++ toBytesGT n)

/-- Encode/decode inverse on canonical byte encodings: if `s` is a canonical
    byte encoding and `decode s = some bytes`, then `encode bytes = s`. -/
def spec_encode_decode_canonical_inverse (impl : RepoImpl) : Prop :=
  ∀ (s : String) (bytes : Bytes),
    isCanonicalByteEncodingGT s = true →
      impl.base58.decode s = some bytes →
        impl.base58.encode bytes = s

/-- Leading-zero count agreement: whenever `decode s = some bytes`, the
    leading-zero-byte count of `bytes` equals the leading-`'1'` count of `s`. -/
def spec_decode_leading_zero_count_exact (impl : RepoImpl) : Prop :=
  ∀ (s : String) (bytes : Bytes),
    impl.base58.decode s = some bytes →
      leadingZeroBytesGT bytes = leadingOnes s.toList

/-- Byte-encode injectivity: `encode` is injective on in-range byte strings —
    equal encodings of two byte strings (all bytes `< 256`) force the byte
    strings equal. -/
def spec_encode_bytes_injective (impl : RepoImpl) : Prop :=
  ∀ a b : Bytes,
    (∀ x ∈ a, x < 256) →
      (∀ x ∈ b, x < 256) →
        impl.base58.encode a = impl.base58.encode b → a = b

/-- Byte-encode length band: for a nonzero significant suffix `b :: rest` whose
    big-endian value lies in `[58^(k-1), 58^k)`, the encoding of `z` zero bytes
    prepended to it has length `z + k`. -/
def spec_encode_byte_length_band (impl : RepoImpl) : Prop :=
  ∀ (z k b : Nat) (rest : Bytes),
    b ≠ 0 → b < 256 → (∀ x ∈ rest, x < 256) →
      1 ≤ k →
        58 ^ (k - 1) ≤ beValueGT (b :: rest) →
          beValueGT (b :: rest) < 58 ^ k →
            (impl.base58.encode (List.replicate z 0 ++ (b :: rest))).length =
              z + k

/-- Byte-decode length band: when `decode s = some bytes` and the significant
    suffix decodes to `v` with `256^(k-1) ≤ v < 256^k`, the decoded byte length
    is `leadingOnes s + k`. -/
def spec_decode_byte_length_band (impl : RepoImpl) : Prop :=
  ∀ (s : String) (bytes : Bytes) (v k : Nat),
    impl.base58.decode s = some bytes →
      impl.base58.decodeInt (significantBase58SuffixGT s) = some v →
        1 ≤ k →
          256 ^ (k - 1) ≤ v →
            v < 256 ^ k →
              bytes.length = leadingOnes s.toList + k

-- ════════════════════════════════════════════════════════════════
-- Concatenation homomorphism, successor/carry, order, congruence, and
-- byte-block combination laws.
--
-- Each states a clean end fact — a whole-string Horner homomorphism, a
-- quotient/remainder decomposition, a leading-block homomorphism, a
-- successor identity, a shortlex order equivalence, a digit-sum
-- congruence, a big-endian block combination, and a canonical-form
-- identity — over all inputs, phrased against frozen ground-truth
-- quantities.
-- ════════════════════════════════════════════════════════════════

/-- The frozen fixed-width base58 numeral for `n` in `k` digits: the base-58
    digit-value expansion of `n` left-padded with `'1'` (zero) digits to width
    `k`, mapped through the frozen alphabet. -/
def fixedWidthBase58NumeralGT (k n : Nat) : String :=
  String.ofList
    (List.replicate (k - (base58DigitValues n).length) '1' ++
      (base58DigitValues n).map b58Char)

/-- The frozen base58 carry-propagation core over a most-significant-first digit
    list: increments the least-significant digit, carrying a `'z'` overflow to
    `'1'` leftward; the `Bool` reports whether the carry escaped the whole list. -/
def base58SuccCoreGT : List Char → Bool × List Char
  | [] => (true, [])
  | c :: rest =>
      let stepped := base58SuccCoreGT rest
      if stepped.fst then
        match b58Idx c with
        | some d =>
            if d + 1 < 58 then (false, b58Char (d + 1) :: stepped.snd)
            else (true, '1' :: stepped.snd)
        | none => (false, c :: stepped.snd)
      else (false, c :: stepped.snd)

/-- The frozen base58 successor of a numeral: apply the carry-propagation core;
    if the carry escaped, prepend the new leading digit `'2'`. -/
def base58SuccNumeralGT (s : String) : String :=
  let stepped := base58SuccCoreGT s.toList
  String.ofList (if stepped.fst then '2' :: stepped.snd else stepped.snd)

/-- The frozen lexicographic order on equal-length character lists by frozen
    alphabet index: the first differing position decides; ties propagate. -/
def base58LexLtGT : List Char → List Char → Bool
  | [], _ => false
  | _, [] => false
  | a :: as, b :: bs =>
      if digitValueGT a < digitValueGT b then true
      else if digitValueGT b < digitValueGT a then false
      else base58LexLtGT as bs

/-- The frozen shortlex order on base58 numerals: shorter numerals come first;
    equal-length numerals are ordered lexicographically by frozen alphabet
    index. -/
def base58ShortLexLtGT (s t : String) : Bool :=
  if s.toList.length < t.toList.length then true
  else if t.toList.length < s.toList.length then false
  else base58LexLtGT s.toList t.toList

/-- The frozen digit-value sum of a numeral: `Σ idx(cᵢ)` over its characters
    (off-alphabet characters contribute `0`). -/
def base58DigitSumGT (s : String) : Nat :=
  (s.toList.map digitValueGT).foldl (fun acc d => acc + d) 0

/-- The frozen canonical form of a valid numeral: drop the leading `'1'` zero
    digits; the empty remainder canonicalizes to the zero numeral `"1"`. -/
def validNumeralCanonicalFormGT (s : String) : String :=
  let rest := significantBase58SuffixGT s
  match rest.toList with
  | [] => "1"
  | _ => rest

/-- Concatenation Horner law: for valid numerals `s` (value `p`) and `t` (value
    `q`), `decodeInt (s ++ t) = p · 58^|t| + q` — appending `t` shifts `s` by one
    radix per suffix digit and adds `t`. -/
def spec_decode_int_concat_homomorphism (impl : RepoImpl) : Prop :=
  ∀ (s t : String) (p q : Nat),
    impl.base58.decodeInt s = some p →
      impl.base58.decodeInt t = some q →
        impl.base58.decodeInt (s ++ t) = some (p * 58 ^ t.toList.length + q)

/-- Concatenation quotient/remainder: for valid numerals `s` (value `p`), `t`
    (value `q`) with concatenated value `n`, dividing `n` by `58^|t|` recovers
    `p` and the remainder is `q`. -/
def spec_decode_int_concat_div_mod (impl : RepoImpl) : Prop :=
  ∀ (s t : String) (p q n : Nat),
    impl.base58.decodeInt s = some p →
      impl.base58.decodeInt t = some q →
        impl.base58.decodeInt (s ++ t) = some n →
          n / 58 ^ t.toList.length = p ∧ n % 58 ^ t.toList.length = q

/-- Leading-zero-byte homomorphism: prepending `z` zero bytes to any byte string
    prepends exactly `z` `'1'`s to its encoding and leaves the rest unchanged —
    `encode (replicate z 0 ++ bytes) = replicate z '1' ++ encode bytes`. -/
def spec_encode_leading_zero_prefix_homomorphism (impl : RepoImpl) : Prop :=
  ∀ (z : Nat) (bytes : Bytes),
    impl.base58.encode (List.replicate z 0 ++ bytes) =
      String.ofList (List.replicate z '1') ++ impl.base58.encode bytes

/-- Leading-`'1'` homomorphism: prepending `z` `'1'`s to any string prepends `z`
    zero bytes to its decode and preserves the success/failure outcome —
    `decode (replicate z '1' ++ s)` is `decode s` with `z` zero bytes prepended
    on success, and `none` exactly when `decode s = none`. -/
def spec_decode_leading_one_prefix_homomorphism (impl : RepoImpl) : Prop :=
  ∀ (z : Nat) (s : String),
    impl.base58.decode (String.ofList (List.replicate z '1') ++ s) =
      match impl.base58.decode s with
      | none => none
      | some bytes => some (List.replicate z 0 ++ bytes)

/-- Fixed-width suffix concatenation: for `q > 0`, `k ≥ 1`, and `r < 58^k`,
    `encodeInt (q · 58^k + r)` is `encodeInt q` followed by the `k`-digit
    (zero-padded) base58 numeral of `r`. -/
def spec_encode_int_fixed_width_concat (impl : RepoImpl) : Prop :=
  ∀ (q r k : Nat), q > 0 → 1 ≤ k → r < 58 ^ k →
    impl.base58.encodeInt (q * 58 ^ k + r) =
      impl.base58.encodeInt q ++ fixedWidthBase58NumeralGT k r

/-- Successor identity: `encodeInt (n + 1)` is the frozen base58 successor of
    `encodeInt n` — increment the least-significant digit, carry `'z'` overflow
    leftward, and grow a new leading `'2'` on total overflow. -/
def spec_encode_int_successor_carry (impl : RepoImpl) : Prop :=
  ∀ n : Nat,
    impl.base58.encodeInt (n + 1) =
      base58SuccNumeralGT (impl.base58.encodeInt n)

/-- Shortlex order embedding: for canonical numerals `s` (value `m`) and `t`
    (value `n`), the frozen shortlex order on `s` and `t` holds iff `m < n` —
    canonical numerals order by length then by frozen alphabet index exactly as
    their values order. -/
def spec_decode_int_canonical_shortlex_order_embedding (impl : RepoImpl) : Prop :=
  ∀ (s t : String) (m n : Nat),
    isCanonicalNumeral s = true →
      isCanonicalNumeral t = true →
        impl.base58.decodeInt s = some m →
          impl.base58.decodeInt t = some n →
            (base58ShortLexLtGT s t = true ↔ m < n)

/-- Digit-sum congruence: for a valid numeral `s` of value `n`, `n` and the
    frozen digit-value sum of `s` are congruent modulo `57` —
    `n % 57 = base58DigitSumGT s % 57`. -/
def spec_decode_int_digit_sum_mod57 (impl : RepoImpl) : Prop :=
  ∀ (s : String) (n : Nat),
    allValid s = true →
      impl.base58.decodeInt s = some n →
        n % 57 = base58DigitSumGT s % 57

/-- Big-endian block combination: `z` zero bytes followed by two significant
    blocks (`b :: left` with `b ≠ 0`, then `right`) encodes to `z` `'1'`s
    followed by the `encodeInt` of the combined big-endian value
    `beValueGT (b :: left) · 256^|right| + beValueGT right`. -/
def spec_encode_append_big_endian_blocks (impl : RepoImpl) : Prop :=
  ∀ (z b : Nat) (left right : Bytes), b ≠ 0 →
    impl.base58.encode (List.replicate z 0 ++ ((b :: left) ++ right)) =
      String.ofList (List.replicate z '1') ++
        impl.base58.encodeInt (beValueGT (b :: left) * 256 ^ right.length + beValueGT right)

/-- Canonical-form re-encoding: for a valid numeral `s` of value `n`,
    `encodeInt n` is the frozen canonical form of `s` — its leading `'1'`s
    dropped, with the empty remainder mapping to the zero numeral `"1"`. -/
def spec_decode_int_reencode_valid_canonical_form (impl : RepoImpl) : Prop :=
  ∀ (s : String) (n : Nat),
    allValid s = true →
      impl.base58.decodeInt s = some n →
        impl.base58.encodeInt n = validNumeralCanonicalFormGT s

end Base58Spec
