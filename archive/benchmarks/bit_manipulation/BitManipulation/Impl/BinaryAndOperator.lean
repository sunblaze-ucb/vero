-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BitManipulation.Impl.BinaryAndOperator

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BitManipulation

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev BinaryAndSig := Int → Int → String

end BitManipulation

-- !benchmark @start global_aux
namespace BitManipulation.BinaryAnd

partial def natToBinChars (n : Nat) : List Char :=
  let rec go (n : Nat) (acc : List Char) : List Char :=
    if n = 0 then acc else
      go (n / 2) ((if n % 2 = 1 then '1' else '0') :: acc)
  if n = 0 then ['0'] else go n []

def zfill (cs : List Char) (n : Nat) : List Char :=
  let pad := n - cs.length
  List.replicate pad '0' ++ cs

end BitManipulation.BinaryAnd
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=binary_and
-- !benchmark @end code_aux def=binary_and

def BitManipulation.binary_and : BitManipulation.BinaryAndSig :=
-- !benchmark @start code def=binary_and
  fun a b =>
    if a < 0 ∨ b < 0 then "" else
      let aBin := BitManipulation.BinaryAnd.natToBinChars a.toNat
      let bBin := BitManipulation.BinaryAnd.natToBinChars b.toNat
      let maxLen := Nat.max aBin.length bBin.length
      let aPad := BitManipulation.BinaryAnd.zfill aBin maxLen
      let bPad := BitManipulation.BinaryAnd.zfill bBin maxLen
      let combined := (aPad.zip bPad).map (fun p =>
        if p.1 = '1' ∧ p.2 = '1' then '1' else '0')
      "0b" ++ String.mk combined
-- !benchmark @end code def=binary_and
