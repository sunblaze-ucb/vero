-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.Ordered

Ordered-list vocabulary translated from Coq's `Ordered.v`. This module
has no scored API slots; the inductive predicate below is frozen
vocabulary used by downstream specifications.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

inductive ordered {A : Type} (order : A → A → Prop) : List A → Prop where
  | ordered_nil : ordered order []
  | ordered_one : ∀ a : A, ordered order [a]
  | ordered_cons :
      ∀ (a b : A) (l : List A),
        order a b → ordered order (b :: l) → ordered order (a :: b :: l)

namespace Huffman

end Huffman
