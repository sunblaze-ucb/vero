/-!
# SequencesV2.Impl.Trusted

Trusted external arithmetic and relation vocabulary used by the sequence
benchmarks. These definitions model Dafny library dependencies outside the
scored API surface.

DO NOT MODIFY trusted helper definitions — these are fixed vocabulary.
-/

namespace SequencesV2

def PowNat (base exp : Nat) : Nat :=
  base ^ exp

def Relations_TotalOrdering {T : Type} (le : T → T → Bool) : Prop :=
  (∀ x, le x x = true) ∧
    (∀ x y, le x y = true ∨ le y x = true) ∧
    (∀ x y z, le x y = true → le y z = true → le x z = true)

def Relations_SortedBy {T : Type} (xs : List T) (le : T → T → Bool) : Prop :=
  ∀ i j, i < j → j < xs.length →
    match xs[i]?, xs[j]? with
    | some x, some y => le x y = true
    | _, _ => True

def Relations_LemmaNewFirstElementStillSortedBy {T : Type} (x : T) (xs : List T) (le : T → T → Bool) : Prop :=
  Relations_SortedBy xs le →
    (∀ y, y ∈ xs → le x y = true) →
    Relations_SortedBy (x :: xs) le

end SequencesV2
