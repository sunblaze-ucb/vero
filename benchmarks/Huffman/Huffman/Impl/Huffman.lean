import Huffman.Impl.BTree
import Huffman.Impl.PBTree
import Huffman.Impl.Code
import Huffman.Impl.Frequency
import Huffman.Impl.Restrict
import Huffman.Impl.PBTree2BTree
import Huffman.Impl.Weight
import Huffman.Impl.Build
import Huffman.Impl.CoverMin
import Huffman.Impl.AuxLib
import Huffman.Impl.Ordered
import Huffman.Impl.WeightTree
import Huffman.Impl.ISort

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.Huffman

Top-level Huffman construction translated from Coq's `Huffman.v`. The
proof-bearing auxiliary construction is frozen curator vocabulary, while the
public `huffman` API is exposed as an opaque reference implementation.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev HuffmanAuxType (A : Type) [DecidableEq A] (empty : A) (m : List A)
    (l : List (Nat × Code A)) : Type :=
  l ≠ [] →
  ordered (fun x y => x.1 ≤ y.1) l →
  (∀ a, a ∈ l →
    Huffman.compute_code A (Huffman.to_btree A (Huffman.pbbuild A empty a.2)) = a.2) →
  (∀ a, a ∈ l →
    Huffman.sum_leaves A (fun x => Huffman.number_of_occurrences A x m)
      (Huffman.to_btree A (Huffman.pbbuild A empty a.2)) = a.1) →
  (∀ a, a ∈ l → a.2 ≠ []) →
  {c : Code A //
    Huffman.compute_code A (Huffman.to_btree A (Huffman.pbbuild A empty c)) = c ∧
    build
      (fun x => Huffman.number_of_occurrences A x m)
      (l.map (fun x => Huffman.to_btree A (Huffman.pbbuild A empty x.2)))
      (Huffman.to_btree A (Huffman.pbbuild A empty c))}

/- requires_human_review: proof-bearing helper from Coq
Program Definition huffman_aux_F (l1 : list (nat * code A))
 (huffman_aux_rec : forall l2 : list (nat * code A), length l2 < length l1 → huffman_aux_type l2) :
 huffman_aux_type l1 :=
match l1 with
| [] => eq_rect [] huffman_aux_type (fun _ _ _ _ _ => False_rect _ _) _ _
| (n1, c1) :: [] => fun nnil ord cc sl lin => exist _ c1 _
| (n1, c1) :: (n2, c2) :: l0 => fun nnil ord cc sl lin =>
  let (c3, _) :=
   huffman_aux_rec
     (insert (fun x y => fst x <=? fst y)
      (n1 + n2,
       map (fun x => (fst x, false :: snd x)) c1 ++
        map (fun x => (fst x, true :: snd x)) c2) l0) _ _ _ _ _ _
  in exist _ c3 _
end.
-/
axiom huffman_aux_F :
  {A : Type} → [DecidableEq A] → (empty : A) → (m : List A) →
  (l1 : List (Nat × Code A)) →
  ((l2 : List (Nat × Code A)) → List.length l2 < List.length l1 → HuffmanAuxType A empty m l2) →
  HuffmanAuxType A empty m l1

/- requires_human_review: proof-bearing helper from Coq
Definition huffman_aux : forall l : list (nat * code A), huffman_aux_type l :=
 list_length_induction (nat * code A) huffman_aux_type huffman_aux_F.
-/
axiom huffman_aux :
  {A : Type} → [DecidableEq A] → (empty : A) → (m : List A) →
  (l : List (Nat × Code A)) → HuffmanAuxType A empty m l

namespace Huffman

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev HuffmanSig :=
  (A : Type) → [DecidableEq A] → (empty : A) → (m : List A) →
    {c : Code A //
      unique_prefix c ∧
      in_alphabet m c ∧
      ∀ c1 : Code A,
        unique_prefix c1 →
        in_alphabet m c1 →
        Huffman.weight A m c ≤ Huffman.weight A m c1}

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=huffman
-- !benchmark @end code_aux def=huffman

axiom Huffman.huffman_witness : Huffman.HuffmanSig

-- !benchmark @start code def=huffman
noncomputable def Huffman.huffman : Huffman.HuffmanSig := Huffman.huffman_witness
-- !benchmark @end code def=huffman
