import Huffman.Impl.UniqueKey
import Huffman.Impl.Code
import Huffman.Impl.Frequency

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.Weight

Weight-related code operations translated from Coq's `Weight.v`. The
reference implementations restrict a code to the symbols present in a message
and compute the bit length of an encoding.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace Huffman

abbrev WeightRestrictCodeSig := (A : Type) → [DecidableEq A] → List A → Code A → Code A
abbrev WeightSig := (A : Type) → [DecidableEq A] → List A → Code A → Nat

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=weight_restrict_code
-- !benchmark @end code_aux def=weight_restrict_code

def Huffman.weight_restrict_code : Huffman.WeightRestrictCodeSig :=
-- !benchmark @start code def=weight_restrict_code
  fun A inst m c =>
    let _ := inst
    List.map
      (fun x : A × Nat => (Prod.fst x, Huffman.find_code A (Prod.fst x) c))
      (Huffman.frequency_list A m)
-- !benchmark @end code def=weight_restrict_code

-- !benchmark @start code_aux def=weight
-- !benchmark @end code_aux def=weight

def Huffman.weight : Huffman.WeightSig :=
-- !benchmark @start code def=weight
  fun A inst m c =>
    let _ := inst
    List.length (Huffman.encode A c m)
-- !benchmark @end code def=weight
