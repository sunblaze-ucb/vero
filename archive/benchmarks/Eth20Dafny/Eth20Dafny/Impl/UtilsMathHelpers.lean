-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eth20Dafny.Impl.UtilsMathHelpers

Helper arithmetic utilities for the Eth20Dafny benchmark, including power-of-two
helpers and range generation.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Eth20Dafny

def power2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * power2 n

def isPowerOf2 (n : Nat) : Prop := ∃ k : Nat, power2 k = n

def min (a : Nat) (b : Nat) : Nat :=
  if a < b then a else b

def max (a : Nat) (b : Nat) : Nat :=
  if a > b then a else b

def range (start : Nat) (stop : Nat) : List Nat :=
  (List.range (stop - start)).map (fun i => start + i)

abbrev GetNextPowerOfTwoSig := Nat → Nat
abbrev GetPrevPowerOfTwoSig := Nat → Nat

end Eth20Dafny

-- !benchmark @start code_aux def=get_next_power_of_two
-- !benchmark @end code_aux def=get_next_power_of_two
def Eth20Dafny.get_next_power_of_two : Eth20Dafny.GetNextPowerOfTwoSig :=
-- !benchmark @start code def=get_next_power_of_two
  fun n =>
    let candidates := (List.range (n + 1)).map (fun k => Eth20Dafny.power2 k)
    match candidates.find? (fun x => n ≤ x) with
    | some value => value
    | none => 1
-- !benchmark @end code def=get_next_power_of_two

-- !benchmark @start code_aux def=get_prev_power_of_two
-- !benchmark @end code_aux def=get_prev_power_of_two
def Eth20Dafny.get_prev_power_of_two : Eth20Dafny.GetPrevPowerOfTwoSig :=
-- !benchmark @start code def=get_prev_power_of_two
  fun n =>
    let candidates := (List.range (n + 1)).map (fun k => Eth20Dafny.power2 k)
    candidates.foldl (fun acc value => if value ≤ n then value else acc) 1
-- !benchmark @end code def=get_prev_power_of_two
