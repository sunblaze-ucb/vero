import Huffman.Impl.WeightTree
import Huffman.Impl.Weight
import Huffman.Impl.BTree
import Huffman.Impl.SameSumLeaves
import Huffman.Impl.ISort
import Huffman.Impl.Cover
import Huffman.Impl.CoverMin
import Huffman.Impl.AuxLib
import Huffman.Impl.Ordered
import Huffman.Impl.OneStep

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.Build

Build-process vocabulary and opaque construction APIs translated from
Coq's `Build.v`. The inductive `build` predicate is frozen vocabulary;
the API declarations below expose the selected construction functions.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

inductive build {A : Type} (f : A → Nat) : List (BTree A) → BTree A → Prop where
  | build_one : ∀ t, build f [t] t
  | build_step : ∀ l1 l2 t, one_step f l1 l2 → build f l2 t → build f l1 t

namespace Huffman

abbrev BuildFunSig :=
  (A : Type) → (f : A → Nat) → (l : List (BTree A)) → l ≠ [] → {t : BTree A // cover_min A f l t}

abbrev BuildfSig :=
  (A : Type) → (f : A → Nat) → (l : List (BTree A)) → l ≠ [] → {t : BTree A // build f l t}

abbrev ObuildfSig :=
  (A : Type) → (f : A → Nat) → (l : List (BTree A)) → l ≠ [] →
    ordered (fun x y => Huffman.sum_leaves A f x ≤ Huffman.sum_leaves A f y) l →
    {t : BTree A // build f l t}

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=build_fun
-- !benchmark @end code_aux def=build_fun

axiom Huffman.build_fun_witness : Huffman.BuildFunSig

-- !benchmark @start code def=build_fun
noncomputable def Huffman.build_fun : Huffman.BuildFunSig := Huffman.build_fun_witness
-- !benchmark @end code def=build_fun

-- !benchmark @start code_aux def=buildf
-- !benchmark @end code_aux def=buildf

axiom Huffman.buildf_witness : Huffman.BuildfSig

-- !benchmark @start code def=buildf
noncomputable def Huffman.buildf : Huffman.BuildfSig := Huffman.buildf_witness
-- !benchmark @end code def=buildf

-- !benchmark @start code_aux def=obuildf
-- !benchmark @end code_aux def=obuildf

axiom Huffman.obuildf_witness : Huffman.ObuildfSig

-- !benchmark @start code def=obuildf
noncomputable def Huffman.obuildf : Huffman.ObuildfSig := Huffman.obuildf_witness
-- !benchmark @end code def=obuildf
