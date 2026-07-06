-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BitManipulation.Impl.BinaryOrOperator

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BitManipulation

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev BinaryOrSig := Int → Int → String

end BitManipulation

-- !benchmark @start global_aux
namespace BitManipulation.BinaryOr

partial def natToBinChars (n : Nat) : List Char :=
  let rec go (n : Nat) (acc : List Char) : List Char :=
    if n = 0 then acc else
      go (n / 2) ((if n % 2 = 1 then '1' else '0') :: acc)
  if n = 0 then ['0'] else go n []

def zfill (cs : List Char) (n : Nat) : List Char :=
  let pad := n - cs.length
  List.replicate pad '0' ++ cs

end BitManipulation.BinaryOr
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=binary_or
-- !benchmark @end code_aux def=binary_or

def BitManipulation.binary_or : BitManipulation.BinaryOrSig :=
-- !benchmark @start code def=binary_or
  fun a b =>
    if a < 0 ∨ b < 0 then "" else
      let aBin := BitManipulation.BinaryOr.natToBinChars a.toNat
      let bBin := BitManipulation.BinaryOr.natToBinChars b.toNat
      let maxLen := Nat.max aBin.length bBin.length
      let aPad := BitManipulation.BinaryOr.zfill aBin maxLen
      let bPad := BitManipulation.BinaryOr.zfill bBin maxLen
      let combined := (aPad.zip bPad).map (fun p =>
        if p.1 = '1' ∨ p.2 = '1' then '1' else '0')
      "0b" ++ String.mk combined
-- !benchmark @end code def=binary_or
