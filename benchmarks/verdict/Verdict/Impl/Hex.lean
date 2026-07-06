import Verdict.Impl.Crypto

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.Hex

Uppercase hex encoding for byte arrays. `specToHexUpper` is the
mathematical specification (curator-given, fully defined — mirrors
Verus's `closed spec fn spec_to_hex_upper` with a concrete recursive
body). `toHexUpper` is the exec-level API (benchmark task) whose
`ensures` clause in Verus couples it to `specToHexUpper`.

Upstream:
- `verdict/src/hash.rs:20-27`
  - `pub closed spec fn spec_to_hex_upper(data: Seq<u8>) -> Seq<char>`
  - `pub fn to_hex_upper(data: &[u8]) -> String`
    with `ensures res@ == spec_to_hex_upper(data@)`.
-/

namespace Verdict

-- ── Vocabulary (DO NOT MODIFY) ──────────────────────────────

/-- Uppercase hex digit for a nibble `0..15`. Verus:
    `HEX_UPPER : [char; 16] = ['0','1',…,'E','F']` in `hash.rs:14`. -/
def hexUpperDigit : UInt8 → Char
  | 0  => '0' | 1  => '1' | 2  => '2' | 3  => '3'
  | 4  => '4' | 5  => '5' | 6  => '6' | 7  => '7'
  | 8  => '8' | 9  => '9' | 10 => 'A' | 11 => 'B'
  | 12 => 'C' | 13 => 'D' | 14 => 'E' | 15 => 'F'
  | _  => '?'  -- unreachable for nibble inputs 0..15

/-- Spec-level hex encoding: every byte emits two uppercase hex
    characters, most-significant nibble first. Curator-given (not a
    benchmark task). Verus: `spec_to_hex_upper` in `hash.rs:20`. -/
def specToHexUpper : List UInt8 → String
  | []         => ""
  | b :: rest  =>
      String.ofList [hexUpperDigit (b / 16), hexUpperDigit (b % 16)]
        ++ specToHexUpper rest

-- ── API signature (DO NOT MODIFY) ───────────────────────────

/-- Exec-level hex encoding: uppercase hexadecimal string for a byte
    sequence. Must agree pointwise with `specToHexUpper`.
    Verus: `to_hex_upper` in `verdict/src/hash.rs:27`. -/
abbrev ToHexUpperSig := Bytes → String

end Verdict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation ──────────────────────────────────────────

-- !benchmark @start code_aux def=toHexUpper
-- !benchmark @end code_aux def=toHexUpper

def Verdict.toHexUpper : Verdict.ToHexUpperSig :=
-- !benchmark @start code def=toHexUpper
  sorry
-- !benchmark @end code def=toHexUpper
