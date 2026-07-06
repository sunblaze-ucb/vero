-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BitManipulation.Impl.SingleBitManipulationOperations

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BitManipulation

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev SetBitSig := Int → Int → Int
abbrev ClearBitSig := Int → Int → Int
abbrev FlipBitSig := Int → Int → Int
abbrev IsBitSetSig := Int → Int → Bool
abbrev GetBitSig := Int → Int → Int

end BitManipulation

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=set_bit
-- !benchmark @end code_aux def=set_bit

def BitManipulation.set_bit : BitManipulation.SetBitSig :=
-- !benchmark @start code def=set_bit
  fun number position =>
    let n := number.toNat
    let p := position.toNat
    ((n ||| (1 <<< p) : Nat) : Int)
-- !benchmark @end code def=set_bit

-- !benchmark @start code_aux def=clear_bit
-- !benchmark @end code_aux def=clear_bit

def BitManipulation.clear_bit : BitManipulation.ClearBitSig :=
-- !benchmark @start code def=clear_bit
  fun number position =>
    let n := number.toNat
    let p := position.toNat
    let mask : Nat := 1 <<< p
    let cleared : Nat := if (n >>> p) % 2 = 1 then n - mask else n
    (cleared : Int)
-- !benchmark @end code def=clear_bit

-- !benchmark @start code_aux def=flip_bit
-- !benchmark @end code_aux def=flip_bit

def BitManipulation.flip_bit : BitManipulation.FlipBitSig :=
-- !benchmark @start code def=flip_bit
  fun number position =>
    let n := number.toNat
    let p := position.toNat
    ((n ^^^ (1 <<< p) : Nat) : Int)
-- !benchmark @end code def=flip_bit

-- !benchmark @start code_aux def=is_bit_set
-- !benchmark @end code_aux def=is_bit_set

def BitManipulation.is_bit_set : BitManipulation.IsBitSetSig :=
-- !benchmark @start code def=is_bit_set
  fun number position =>
    let n := number.toNat
    let p := position.toNat
    decide ((n >>> p) % 2 = 1)
-- !benchmark @end code def=is_bit_set

-- !benchmark @start code_aux def=get_bit
-- !benchmark @end code_aux def=get_bit

def BitManipulation.get_bit : BitManipulation.GetBitSig :=
-- !benchmark @start code def=get_bit
  fun number position =>
    let n := number.toNat
    let p := position.toNat
    (((n >>> p) % 2 : Nat) : Int)
-- !benchmark @end code def=get_bit
