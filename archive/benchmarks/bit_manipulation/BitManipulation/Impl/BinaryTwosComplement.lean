-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BitManipulation.Impl.BinaryTwosComplement

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BitManipulation

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev TwosComplementSig := Int → String

end BitManipulation

-- !benchmark @start global_aux
namespace BitManipulation.TwosComplement

partial def natToBinChars (n : Nat) : List Char :=
  let rec go (n : Nat) (acc : List Char) : List Char :=
    if n = 0 then acc else
      go (n / 2) ((if n % 2 = 1 then '1' else '0') :: acc)
  if n = 0 then ['0'] else go n []

end BitManipulation.TwosComplement
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=twos_complement
-- !benchmark @end code_aux def=twos_complement

def BitManipulation.twos_complement : BitManipulation.TwosComplementSig :=
-- !benchmark @start code def=twos_complement
  fun number =>
    if number > 0 then "" else
    if number = 0 then "0b0" else
      let absN := number.natAbs
      let absBits := BitManipulation.TwosComplement.natToBinChars absN
      let L := absBits.length
      let twosVal := (2 ^ (L + 1) : Nat) - absN
      let twosBits := BitManipulation.TwosComplement.natToBinChars twosVal
      let pad := (L + 1) - twosBits.length
      "0b" ++ String.mk (List.replicate pad '0' ++ twosBits)
-- !benchmark @end code def=twos_complement
