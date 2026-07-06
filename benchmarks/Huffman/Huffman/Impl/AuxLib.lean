-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.AuxLib

Auxiliary list functions and theorem-vocabulary helpers translated from
Coq's `AuxLib.v`. This module has no scored API slots; the executable
helpers below are frozen vocabulary used by downstream specifications.
-/

def split_one {A : Type} : List A → List (A × List A)
  | [] => []
  | a :: l => (a, l) :: (split_one l).map (fun p => (p.1, a :: p.2))

def all_permutations_aux {A : Type} (l : List A) : Nat → List (List A)
  | 0 => [[]]
  | n + 1 => (split_one l).flatMap (fun p => (all_permutations_aux p.2 n).map (fun q => p.1 :: q))

def all_permutations {A : Type} (l : List A) : List (List A) :=
  all_permutations_aux l l.length

def find_max {A : Type} (f : A → Nat) : List A → Option (Nat × A)
  | [] => none
  | a :: l =>
      match find_max f l with
      | none => some (f a, a)
      | some (n, b) => if n ≤ f a then some (f a, a) else some (n, b)

def find_min {A : Type} (f : A → Nat) : List A → Option (Nat × A)
  | [] => none
  | a :: l =>
      match find_min f l with
      | none => some (f a, a)
      | some (n, b) => if n ≤ f a then some (n, b) else some (f a, a)

def map2 {A B C : Type} (f : A → B → C) : List A → List B → List C
  | [], _ => []
  | _, [] => []
  | a :: l1, b :: l2 => f a b :: map2 f l1 l2

def Permutation_dec : Prop :=
  True

def helper_list_length_ind : Prop :=
  ∀ (A B C : Type), ∀ P : List A → Prop,
    (∀ l1 : List A, (∀ l2 : List A, List.length l2 < List.length l1 → P l2) → P l1) →
    ∀ l : List A, P l

def list_length_induction : Prop :=
  True

def helper_permutation_all_permutations_aux : Prop :=
  ∀ (A B C : Type), ∀ (n : Nat) (l1 l2 : List A),
    n = List.length l2 → List.Perm l1 l2 → l1 ∈ all_permutations_aux l2 n

namespace Huffman

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux
