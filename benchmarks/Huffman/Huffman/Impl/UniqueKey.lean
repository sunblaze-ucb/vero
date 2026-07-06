-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.UniqueKey

Unique-key association-list vocabulary translated from Coq's
`UniqueKey.v`. This module has no scored API slots; the inductive
predicate below is frozen vocabulary used by downstream specifications.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

inductive unique_key {A B : Type} : List (A × B) → Prop where
  | nil : unique_key []
  | cons : ∀ (a : A) (b : B) (l : List (A × B)),
      (∀ b' : B, (a, b') ∉ l) → unique_key l → unique_key ((a, b) :: l)

namespace Huffman

end Huffman
