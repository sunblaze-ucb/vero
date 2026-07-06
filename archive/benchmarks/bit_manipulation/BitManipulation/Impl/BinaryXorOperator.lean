-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BitManipulation.Impl.BinaryXorOperator

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BitManipulation

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev BinaryXorSig := Int → Int → String

end BitManipulation

-- !benchmark @start global_aux
namespace BitManipulation.BinaryXor

partial def natToBinChars (n : Nat) : List Char :=
  let rec go (n : Nat) (acc : List Char) : List Char :=
    if n = 0 then acc else
      go (n / 2) ((if n % 2 = 1 then '1' else '0') :: acc)
  if n = 0 then ['0'] else go n []

def zfill (cs : List Char) (n : Nat) : List Char :=
  let pad := n - cs.length
  List.replicate pad '0' ++ cs

end BitManipulation.BinaryXor
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=binary_xor
-- !benchmark @end code_aux def=binary_xor

def BitManipulation.binary_xor : BitManipulation.BinaryXorSig :=
-- !benchmark @start code def=binary_xor
  fun a b =>
    if a < 0 ∨ b < 0 then "" else
      let aBin := BitManipulation.BinaryXor.natToBinChars a.toNat
      let bBin := BitManipulation.BinaryXor.natToBinChars b.toNat
      let maxLen := Nat.max aBin.length bBin.length
      let aPad := BitManipulation.BinaryXor.zfill aBin maxLen
      let bPad := BitManipulation.BinaryXor.zfill bBin maxLen
      let combined := (aPad.zip bPad).map (fun p =>
        if p.1 ≠ p.2 then '1' else '0')
      "0b" ++ String.mk combined
-- !benchmark @end code def=binary_xor
