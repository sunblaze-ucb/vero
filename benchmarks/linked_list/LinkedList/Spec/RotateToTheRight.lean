import LinkedList.Harness

/-!
# LinkedList.Spec.RotateToTheRight

Specifications for right-rotation linked list operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- rotate_insertNode appends the element to the end, implementing snoc. -/
def spec_rotate_insertNode_snoc (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (data : Int), impl.linkedList.rotate_insertNode l data = l ++ [data]

/-- Rotating by 0 positions is a no-op. -/
def spec_rotate_zero_id (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.rotate_rotateToTheRight l 0 = l

/-- Rotating an empty list by any number of positions yields the empty list. -/
def spec_rotate_empty_id (impl : RepoImpl) : Prop :=
  ∀ (k : Nat), impl.linkedList.rotate_rotateToTheRight [] k = []

/-- When places % l.length = 0, the list is unchanged. -/
def spec_rotate_full_id (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (places : Nat), places % l.length = 0 →
    impl.linkedList.rotate_rotateToTheRight l places = l

/-- Rotation preserves the length of the list. -/
def spec_rotate_length_preserved (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (k : Nat),
    (impl.linkedList.rotate_rotateToTheRight l k).length = l.length

/-- For non-empty l, rotating right by places equals l.drop (n - places % n) ++ l.take (n - places % n). -/
def spec_rotate_split_form (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (places : Nat), l ≠ [] →
    let n := l.length
    impl.linkedList.rotate_rotateToTheRight l places
      = l.drop (n - places % n) ++ l.take (n - places % n)
