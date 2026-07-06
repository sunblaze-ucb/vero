import JsonV2.Harness

/-!
# Json.Spec.Utils.Seq

Frozen specifications for sequence append laws from `JSON.Utils.Seq`.
-/

/-- Appending the empty sequence on the right is neutral. -/
def spec_neutral (impl : RepoImpl) : Prop :=
  ∀ (α : Type) (l : List α), l ++ [] = l

/-- Sequence append is associative. -/
def spec_assoc (impl : RepoImpl) : Prop :=
  ∀ (α : Type) (a b c : List α), (a ++ b) ++ c = a ++ (b ++ c)

/-- Sequence append associativity in the reverse orientation. -/
def spec_assocprime (impl : RepoImpl) : Prop :=
  ∀ (α : Type) (a b c : List α), a ++ (b ++ c) = (a ++ b) ++ c

/-- Four-sequence append reassociates to the right. -/
def spec_assoc2 (impl : RepoImpl) : Prop :=
  ∀ (α : Type) (a b c d : List α), (a ++ b) ++ (c ++ d) = a ++ (b ++ (c ++ d))
