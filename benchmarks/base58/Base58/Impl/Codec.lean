-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Base58.Impl.Codec

Base58 encoding/decoding: a radix-58 positional numeral system over a fixed
58-character alphabet (omitting `0`, `O`, `I`, `l`). Integers are unbounded
`Nat`, bytes are `Nat` in `0…255` carried in a `List Nat`, the encoded form is
a `String`.

The **frozen alphabet** `"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"`
is a curator-fixed constant shared verbatim by the implementation and the
specification's ground truth; it is not a free choice, and the radix is `58`.

The four APIs:

* `decodeInt s` — the positional integer value of a base58 numeral `s`; `none`
  if any character is outside the alphabet, `some 0` for the empty string.
* `encodeInt n` — the canonical base58 numeral for `n` (`0` is the single
  zero-digit `"1"`, and positives carry no redundant leading `"1"`).
* `encode bytes` — the base58 encoding of a byte string, with leading zero
  bytes mapped to leading `"1"`s.
* `decode s` — the inverse of `encode`.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Frozen alphabet + index/char tables (DO NOT MODIFY) ──────────

/-- The frozen Bitcoin base58 alphabet, as a `String`. 58 characters, omitting
    the visually ambiguous `0`, `O`, `I`, `l`. This is a curator-fixed constant
    shared verbatim by the implementation and the specification's ground truth;
    it is not a free choice. -/
def b58AlphabetStr : String :=
  "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

/-- The frozen alphabet as a character list. -/
def b58Alphabet : List Char := b58AlphabetStr.toList

/-- `b58Idx c`: the base58 digit value of character `c` — its index in the
    frozen alphabet — or `none` if `c` is not a base58 character. -/
def b58Idx (c : Char) : Option Nat := b58Alphabet.idxOf? c

/-- `b58Char n`: the `n`-th frozen-alphabet character. Out-of-range indices fall
    back to `'1'` (the zero digit); callers only ever pass `n < 58`. -/
def b58Char (n : Nat) : Char := b58Alphabet.getD n '1'

-- A byte string: each entry is a byte value in `0…255` (not range-enforced in
-- the type; the convention is documented on the APIs).
abbrev Bytes := List Nat

namespace Base58

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────

/-- `decodeInt s`: the positional integer value of the base58 numeral `s`, or
    `none` if any character is outside the frozen alphabet. -/
abbrev DecodeIntSig := String → Option Nat

/-- `encodeInt n`: the canonical base58 numeral for the integer `n`. -/
abbrev EncodeIntSig := Nat → String

/-- `encode bytes`: the base58 encoding of a byte string (leading zero bytes
    map to leading `"1"`s). -/
abbrev EncodeSig := Bytes → String

/-- `decode s`: the byte string decoded from the base58 string `s`, or `none`
    if the non-`"1"` portion contains an invalid character. -/
abbrev DecodeSig := String → Option Bytes

end Base58

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=decodeInt
-- !benchmark @end code_aux def=decodeInt

def Base58.decodeInt : Base58.DecodeIntSig :=
-- !benchmark @start code def=decodeInt
  fun s => s.toList.foldl
    (fun acc c =>
      match acc, b58Idx c with
      | some n, some d => some (n * 58 + d)
      | _, _ => none)
    (some 0)
-- !benchmark @end code def=decodeInt

-- !benchmark @start code_aux def=encodeInt
/-- Helper for `encodeInt`; `fuel` bounds the recursion (the API passes `n`). -/
def encodeIntAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | _, 0, acc => acc
  | fuel + 1, n, acc => encodeIntAux fuel (n / 58) (b58Char (n % 58) :: acc)
-- !benchmark @end code_aux def=encodeInt

def Base58.encodeInt : Base58.EncodeIntSig :=
-- !benchmark @start code def=encodeInt
  fun n => if n == 0 then "1" else String.ofList (encodeIntAux n n [])
-- !benchmark @end code def=encodeInt

-- !benchmark @start code_aux def=encode
/-- Count of leading zero bytes. -/
def leadingZeroBytes : Bytes → Nat
  | [] => 0
  | b :: rest => if b == 0 then leadingZeroBytes rest + 1 else 0

/-- Drop the leading zero bytes, returning the significant suffix. -/
def dropLeadingZeroBytes : Bytes → Bytes
  | [] => []
  | b :: rest => if b == 0 then dropLeadingZeroBytes rest else b :: rest

/-- Big-endian integer value of a byte string (`Σ bᵢ · 256^k`). -/
def beValue (bytes : Bytes) : Nat := bytes.foldl (fun acc b => acc * 256 + b) 0
-- !benchmark @end code_aux def=encode

def Base58.encode : Base58.EncodeSig :=
-- !benchmark @start code def=encode
  fun bytes =>
    let z := leadingZeroBytes bytes
    let rest := dropLeadingZeroBytes bytes
    let body := if rest.isEmpty then "" else Base58.encodeInt (beValue rest)
    String.ofList (List.replicate z '1') ++ body
-- !benchmark @end code def=encode

-- !benchmark @start code_aux def=decode
/-- Big-endian byte expansion of a `Nat` (no leading zero bytes). `fuel` bounds
    the recursion; the API passes `n`, which dominates the byte count. -/
def toBytesAux : Nat → Nat → Bytes → Bytes
  | 0, _, acc => acc
  | _, 0, acc => acc
  | fuel + 1, n, acc => toBytesAux fuel (n / 256) ((n % 256) :: acc)

/-- Big-endian byte expansion of a `Nat`; `0` expands to the empty byte string. -/
def toBytes (n : Nat) : Bytes := if n == 0 then [] else toBytesAux n n []
-- !benchmark @end code_aux def=decode

def Base58.decode : Base58.DecodeSig :=
-- !benchmark @start code def=decode
  fun s =>
    let z := (s.toList.takeWhile (· == '1')).length
    let restChars := s.toList.dropWhile (· == '1')
    match Base58.decodeInt (String.ofList restChars) with
    | none => none
    | some v => some (List.replicate z 0 ++ toBytes v)
-- !benchmark @end code def=decode
