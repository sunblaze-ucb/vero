import Huffman.Impl.UniqueKey

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.Frequency

Frequency-list helpers translated from Coq's `Frequency.v`. The frozen
helper `id_list` expands an element into repeated occurrences; the scored APIs
build and query frequency lists.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

def id_list {A : Type} (a : A) : Nat → List A
  | 0 => []
  | n + 1 => a :: id_list a n

namespace Huffman

abbrev AddFrequencyListSig :=
  (A : Type) → [DecidableEq A] → A → List (A × Nat) → List (A × Nat)

abbrev FrequencyListSig :=
  (A : Type) → [DecidableEq A] → List A → List (A × Nat)

abbrev NumberOfOccurrencesSig :=
  (A : Type) → [DecidableEq A] → A → List A → Nat

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=add_frequency_list
-- !benchmark @end code_aux def=add_frequency_list

def Huffman.add_frequency_list : Huffman.AddFrequencyListSig :=
-- !benchmark @start code def=add_frequency_list
  fun (A : Type) [DecidableEq A] a l =>
    let rec go : List (A × Nat) → List (A × Nat)
      | [] => [(a, 1)]
      | (b, n) :: l1 =>
          if a = b then
            (a, n + 1) :: l1
          else
            (b, n) :: go l1
    go l
-- !benchmark @end code def=add_frequency_list

-- !benchmark @start code_aux def=frequency_list
-- !benchmark @end code_aux def=frequency_list

def Huffman.frequency_list : Huffman.FrequencyListSig :=
-- !benchmark @start code def=frequency_list
  fun (A : Type) [DecidableEq A] l =>
    let rec go : List A → List (A × Nat)
      | [] => []
      | a :: l1 => Huffman.add_frequency_list A a (go l1)
    go l
-- !benchmark @end code def=frequency_list

-- !benchmark @start code_aux def=number_of_occurrences
-- !benchmark @end code_aux def=number_of_occurrences

def Huffman.number_of_occurrences : Huffman.NumberOfOccurrencesSig :=
-- !benchmark @start code def=number_of_occurrences
  fun (A : Type) [DecidableEq A] a l =>
    let rec go : List A → Nat
      | [] => 0
      | b :: l1 =>
          if a = b then
            go l1 + 1
          else
            go l1
    go l
-- !benchmark @end code def=number_of_occurrences
