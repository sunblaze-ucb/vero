import Huffman.Impl.Ordered

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.ISort

Insertion sort translated from Coq's `ISort.v`. The executable reference
implementations below sort by repeatedly inserting elements according to a
decidable ordering function.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Huffman

abbrev InsertSig := (A : Type) → (A → A → Bool) → A → List A → List A
abbrev IsortSig := (A : Type) → (A → A → Bool) → List A → List A

end Huffman

-- !benchmark @start code_aux def=insert
-- !benchmark @end code_aux def=insert

def Huffman.insert : Huffman.InsertSig :=
-- !benchmark @start code def=insert
  fun A order_fun a l =>
    let rec go : List A → List A
      | [] => [a]
      | b :: l1 =>
          if order_fun a b then
            a :: b :: l1
          else
            b :: go l1
    go l
-- !benchmark @end code def=insert

-- !benchmark @start code_aux def=isort
-- !benchmark @end code_aux def=isort

def Huffman.isort : Huffman.IsortSig :=
-- !benchmark @start code def=isort
  fun A order_fun l =>
    let rec sort : List A → List A
      | [] => []
      | b :: l1 => Huffman.insert A order_fun b (sort l1)
    sort l
-- !benchmark @end code def=isort
