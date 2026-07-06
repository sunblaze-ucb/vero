import Huffman.Impl.Code
import Huffman.Impl.UniqueKey

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.PBTree

Partial binary trees and executable conversions between trees, paths, and
codes translated from Coq's `PBTree.v`. Types, helpers, and signatures are
fixed vocabulary; the API bodies are curator reference implementations.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

inductive PBTree (A : Type) where
  | pbleaf : A → PBTree A
  | pbleft : PBTree A → PBTree A
  | pbright : PBTree A → PBTree A
  | pbnode : PBTree A → PBTree A → PBTree A
  deriving Repr, DecidableEq, BEq

inductive inpb {A : Type} : PBTree A → PBTree A → Prop where
  | inpb_leaf : ∀ t, inpb t t
  | inpb_left : ∀ t t1, inpb t t1 → inpb t (PBTree.pbleft t1)
  | inpb_right : ∀ t t1, inpb t t1 → inpb t (PBTree.pbright t1)
  | inpb_node_l : ∀ t t1 t2, inpb t t1 → inpb t (PBTree.pbnode t1 t2)
  | inpb_node_r : ∀ t t1 t2, inpb t t2 → inpb t (PBTree.pbnode t1 t2)

def distinct_pbleaves {A : Type} (t : PBTree A) : Prop :=
  ∀ t0 t1 t2 : PBTree A, inpb (PBTree.pbnode t1 t2) t → inpb t0 t1 → inpb t0 t2 → False

noncomputable def inpb_dec {A : Type} [DecidableEq A] (a b : PBTree A) : Decidable (inpb a b) := by
  classical
  exact Classical.propDecidable _

inductive pbfree {A : Type} : List Bool → PBTree A → Prop where
  | left1  : ∀ (b : PBTree A) (l), pbfree (true :: l) (PBTree.pbleft b)
  | left2  : ∀ (b : PBTree A) (l), pbfree l b → pbfree (false :: l) (PBTree.pbleft b)
  | right1 : ∀ (b : PBTree A) (l), pbfree (false :: l) (PBTree.pbright b)
  | right2 : ∀ (b : PBTree A) (l), pbfree l b → pbfree (true :: l) (PBTree.pbright b)
  | node1  : ∀ (b c : PBTree A) (l), pbfree l b → pbfree (false :: l) (PBTree.pbnode b c)
  | node2  : ∀ (b c : PBTree A) (l), pbfree l b → pbfree (true :: l) (PBTree.pbnode c b)

def pbtree_dec {A : Type} [DecidableEq A] (a b : PBTree A) : Decidable (a = b) :=
  inferInstance

namespace Huffman

abbrev AllPbleavesSig := (A : Type) → PBTree A → List A
abbrev ComputePbcodeSig := (A : Type) → PBTree A → Code A
abbrev PbaddSig := (A : Type) → A → PBTree A → List Bool → PBTree A
abbrev PbbuildSig := (A : Type) → A → Code A → PBTree A

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=all_pbleaves
-- !benchmark @end code_aux def=all_pbleaves

def Huffman.all_pbleaves : Huffman.AllPbleavesSig :=
-- !benchmark @start code def=all_pbleaves
  fun A t =>
    let rec go : PBTree A → List A
      | PBTree.pbleaf a => [a]
      | PBTree.pbleft t1 => go t1
      | PBTree.pbright t1 => go t1
      | PBTree.pbnode t1 t2 => go t1 ++ go t2
    go t
-- !benchmark @end code def=all_pbleaves

-- !benchmark @start code_aux def=compute_pbcode
-- !benchmark @end code_aux def=compute_pbcode

def Huffman.compute_pbcode : Huffman.ComputePbcodeSig :=
-- !benchmark @start code def=compute_pbcode
  fun A t =>
    let rec go : PBTree A → Code A
      | PBTree.pbleaf a => [(a, [])]
      | PBTree.pbleft t1 =>
          (go t1).map (fun v => (v.1, false :: v.2))
      | PBTree.pbright t1 =>
          (go t1).map (fun v => (v.1, true :: v.2))
      | PBTree.pbnode t1 t2 =>
          (go t1).map (fun v => (v.1, false :: v.2)) ++
          (go t2).map (fun v => (v.1, true :: v.2))
    go t
-- !benchmark @end code def=compute_pbcode

-- !benchmark @start code_aux def=pbadd
-- !benchmark @end code_aux def=pbadd

def Huffman.pbadd : Huffman.PbaddSig :=
-- !benchmark @start code def=pbadd
  fun A a t l =>
    let rec go (tree : PBTree A) : List Bool → PBTree A
      | [] => PBTree.pbleaf a
      | false :: rest =>
          match tree with
          | PBTree.pbnode t1 t2 => PBTree.pbnode (go t1 rest) t2
          | PBTree.pbleft t1 => PBTree.pbleft (go t1 rest)
          | PBTree.pbright t2 => PBTree.pbnode (go (PBTree.pbleaf a) rest) t2
          | PBTree.pbleaf _ => PBTree.pbleft (go (PBTree.pbleaf a) rest)
      | true :: rest =>
          match tree with
          | PBTree.pbnode t1 t2 => PBTree.pbnode t1 (go t2 rest)
          | PBTree.pbright t2 => PBTree.pbright (go t2 rest)
          | PBTree.pbleft t1 => PBTree.pbnode t1 (go (PBTree.pbleaf a) rest)
          | PBTree.pbleaf _ => PBTree.pbright (go (PBTree.pbleaf a) rest)
    go t l
-- !benchmark @end code def=pbadd

-- !benchmark @start code_aux def=pbbuild
-- !benchmark @end code_aux def=pbbuild

def Huffman.pbbuild : Huffman.PbbuildSig :=
-- !benchmark @start code def=pbbuild
  fun A empty c =>
    c.foldr (fun p tree => Huffman.pbadd A p.1 tree p.2) (PBTree.pbleaf empty)
-- !benchmark @end code def=pbbuild
