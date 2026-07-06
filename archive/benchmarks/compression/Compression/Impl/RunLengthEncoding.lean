-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Compression.Impl.RunLengthEncoding

Run-Length Encoding (RLE): a simple lossless compression scheme that
replaces consecutive runs of the same character with a `(count, char)`
pair encoded as the decimal count followed by the character.

`run_length_encode` encodes a `String` → `String` (e.g. `"AAABBC"` →
`"3A2B1C"`).  `run_length_decode` is the inverse.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace Compression

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev RunLengthEncodeSig := String → String
abbrev RunLengthDecodeSig := String → String

end Compression

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ──────────────────────────

-- !benchmark @start code_aux def=run_length_encode
-- !benchmark @end code_aux def=run_length_encode

def Compression.run_length_encode : Compression.RunLengthEncodeSig :=
-- !benchmark @start code def=run_length_encode
  fun s =>
    if s.isEmpty then ""
    else
      let chars := s.toList
      -- Walk with foldl tracking (accumulator-string, lastChar, count)
      let (result, lastChar, count) :=
        chars.tail.foldl (fun (acc, lc, n) c =>
          if c == lc then (acc, lc, n + 1)
          else (acc ++ toString n ++ String.singleton lc, c, 1)
        ) ("", chars.head!, 1)
      result ++ toString count ++ String.singleton lastChar
-- !benchmark @end code def=run_length_encode

-- !benchmark @start code_aux def=run_length_decode
-- Parse a decimal prefix from a char list; returns (number, remaining chars).
-- @review human: terminates because chars shrinks until no leading digit.
private partial def parseNat (chars : List Char) (acc : Nat) : Nat × List Char :=
  match chars with
  | [] => (acc, [])
  | c :: rest =>
    if c.isDigit then parseNat rest (acc * 10 + c.toNat - '0'.toNat)
    else (acc, chars)
-- !benchmark @end code_aux def=run_length_decode

-- @review human: termination via list shrinking (≥ 2 chars consumed per iteration)
partial def Compression.run_length_decode : Compression.RunLengthDecodeSig :=
-- !benchmark @start code def=run_length_decode
  fun s =>
    let rec go (chars : List Char) (acc : String) : String :=
      match chars with
      | [] => acc
      | _ =>
        let (n, rest) := parseNat chars 0
        match rest with
        | [] => acc  -- malformed: digit(s) with no following char
        | c :: tail => go tail (acc ++ String.ofList (List.replicate n c))
    go s.toList ""
-- !benchmark @end code def=run_length_decode
