import Huffman.Impl.Code
import Huffman.Impl.UniqueKey

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.BTree

Binary tree vocabulary and executable tree traversals translated from
Coq's `BTree.v`. Types, helpers, and signatures are fixed vocabulary.
Function bodies are the curator's reference implementations and are the
only scored code slots in this module.
-/

inductive BTree (A : Type) where
  | leaf : A → BTree A
  | node : BTree A → BTree A → BTree A
  deriving Repr, DecidableEq, BEq

inductive inb {A : Type} : BTree A → BTree A → Prop where
  | inleaf : ∀ t, inb t t
  | innodeL : ∀ t t1 t2, inb t t1 → inb t (BTree.node t1 t2)
  | innodeR : ∀ t t1 t2, inb t t2 → inb t (BTree.node t1 t2)

def distinct_leaves {A : Type} (t : BTree A) : Prop :=
  ∀ t0 t1 t2 : BTree A, inb (BTree.node t1 t2) t → inb t0 t1 → inb t0 t2 → False

def number_of_nodes {A : Type} : BTree A → Nat
  | BTree.leaf _ => 0
  | BTree.node t1 t2 => Nat.succ (number_of_nodes t1 + number_of_nodes t2)

namespace Huffman

abbrev AllLeavesSig := (A : Type) → BTree A → List A
abbrev ComputeCodeSig := (A : Type) → BTree A → Code A

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=all_leaves
-- !benchmark @end code_aux def=all_leaves

def Huffman.all_leaves : Huffman.AllLeavesSig :=
-- !benchmark @start code def=all_leaves
  fun A t =>
    let rec go : BTree A → List A
      | BTree.leaf a => [a]
      | BTree.node t1 t2 => go t1 ++ go t2
    go t
-- !benchmark @end code def=all_leaves

-- !benchmark @start code_aux def=compute_code
-- !benchmark @end code_aux def=compute_code

def Huffman.compute_code : Huffman.ComputeCodeSig :=
-- !benchmark @start code def=compute_code
  fun A t =>
    let rec go : BTree A → Code A
      | BTree.leaf a => [(a, [])]
      | BTree.node t1 t2 =>
          (go t1).map (fun v => (v.1, false :: v.2)) ++
          (go t2).map (fun v => (v.1, true :: v.2))
    go t
-- !benchmark @end code def=compute_code
