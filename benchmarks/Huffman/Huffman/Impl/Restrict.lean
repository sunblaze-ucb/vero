import Huffman.Impl.Frequency
import Huffman.Impl.Code
import Huffman.Impl.PBTree
import Huffman.Impl.UniqueKey
import Huffman.Impl.Build

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.Restrict

Restriction of a code to the keys appearing in a message frequency list,
translated from Coq's `Restrict.v`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace Huffman

abbrev RestrictCodeSig :=
  (A : Type) → [DecidableEq A] → List A → Code A → Code A

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=restrict_code
-- !benchmark @end code_aux def=restrict_code

def Huffman.restrict_code : Huffman.RestrictCodeSig :=
-- !benchmark @start code def=restrict_code
  fun (A : Type) [DecidableEq A] m c =>
    (Huffman.frequency_list A m).map
      (fun x : A × Nat => (x.1, Huffman.find_code A x.1 c))
-- !benchmark @end code def=restrict_code
