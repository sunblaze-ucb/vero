import VerifiedIronkv.Impl.VerusExtraSeqLibV

/-!
# VerifiedIronkv.Impl.VerusExtraSetLibExtV

Translated Verus vocabulary and reference implementations for `VerusExtraSetLibExtV`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

def set_fold {A B : Type} (f : B → A → B) (init : B) (xs : List A) : B :=
  xs.foldl f init

def flatten_sets {A : Type} (sets : List (List A)) : List A :=
  sets.flatten

def map_fold {A B C : Type} (f : B → A → B) (g : C → A) (init : B) (xs : List C) : B :=
  xs.foldl (fun acc x => f acc (g x)) init

namespace Bank


end Bank

