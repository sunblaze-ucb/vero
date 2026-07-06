-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BitManipulation.Impl.BinaryShifts

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BitManipulation

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev LogicalLeftShiftSig := Int → Int → String
abbrev LogicalRightShiftSig := Int → Int → String
abbrev ArithmeticRightShiftSig := Int → Int → String

end BitManipulation

-- !benchmark @start global_aux
namespace BitManipulation.Shifts

partial def natToBinChars (n : Nat) : List Char :=
  let rec go (n : Nat) (acc : List Char) : List Char :=
    if n = 0 then acc else
      go (n / 2) ((if n % 2 = 1 then '1' else '0') :: acc)
  if n = 0 then ['0'] else go n []

end BitManipulation.Shifts
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=logical_left_shift
-- !benchmark @end code_aux def=logical_left_shift

def BitManipulation.logical_left_shift : BitManipulation.LogicalLeftShiftSig :=
-- !benchmark @start code def=logical_left_shift
  fun number shift_amount =>
    if number < 0 ∨ shift_amount < 0 then "" else
      let bits := BitManipulation.Shifts.natToBinChars number.toNat
      let zeros := List.replicate shift_amount.toNat '0'
      "0b" ++ String.mk bits ++ String.mk zeros
-- !benchmark @end code def=logical_left_shift

-- !benchmark @start code_aux def=logical_right_shift
-- !benchmark @end code_aux def=logical_right_shift

def BitManipulation.logical_right_shift : BitManipulation.LogicalRightShiftSig :=
-- !benchmark @start code def=logical_right_shift
  fun number shift_amount =>
    if number < 0 ∨ shift_amount < 0 then "" else
      let bits := BitManipulation.Shifts.natToBinChars number.toNat
      let s := shift_amount.toNat
      if s ≥ bits.length then "0b0"
      else "0b" ++ String.mk (bits.take (bits.length - s))
-- !benchmark @end code def=logical_right_shift

-- !benchmark @start code_aux def=arithmetic_right_shift
-- !benchmark @end code_aux def=arithmetic_right_shift

def BitManipulation.arithmetic_right_shift : BitManipulation.ArithmeticRightShiftSig :=
-- !benchmark @start code def=arithmetic_right_shift
  fun number shift_amount =>
    -- Build the unshifted binary representation per Python's algorithm.
    let binary_number : List Char :=
      if number ≥ 0 then
        '0' :: BitManipulation.Shifts.natToBinChars number.toNat
      else
        let absN := number.natAbs
        let absBits := BitManipulation.Shifts.natToBinChars absN
        let L := absBits.length
        -- 2's complement value = 2^(L+1) + number = 2^(L+1) - absN.
        let twosVal := (2 ^ (L + 1) : Nat) - absN
        let twosBits := BitManipulation.Shifts.natToBinChars twosVal
        -- twosBits should have exactly L+1 chars; left-pad with '0' if shorter.
        let pad := (L + 1) - twosBits.length
        List.replicate pad '0' ++ twosBits
    let s := shift_amount.toNat
    if s ≥ binary_number.length then
      let signChar := binary_number.headD '0'
      "0b" ++ String.mk (List.replicate binary_number.length signChar)
    else
      let signChar := binary_number.headD '0'
      let signPrefix := List.replicate s signChar
      let kept := binary_number.take (binary_number.length - s)
      "0b" ++ String.mk signPrefix ++ String.mk kept
-- !benchmark @end code def=arithmetic_right_shift
