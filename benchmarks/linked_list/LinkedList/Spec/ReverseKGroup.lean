import LinkedList.Harness

/-!
# LinkedList.Spec.ReverseKGroup

Specifications for k-group reversal operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- revk_append adds an element to the end, implementing snoc. -/
def spec_revk_append_snoc (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.revk_append l a = l ++ [a]

/-- Reference model: reverse each complete chunk of length `k`, leaving the tail unchanged. -/
def spec_helper_reverseKGroups (l : List Int) (k : Nat) : List Int :=
  if k = 0 ∨ k = 1 then l
  else if l.length < k then l
  else (l.take k).reverse ++ spec_helper_reverseKGroups (l.drop k) k
termination_by l.length
decreasing_by
  simp_wf
  omega

/-- Reversing in groups of 0 is a no-op. -/
def spec_revk_reverseKNodes_zero (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.revk_reverseKNodes l 0 = l

/-- Reversing in groups of 1 is a no-op. -/
def spec_revk_reverseKNodes_one (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), impl.linkedList.revk_reverseKNodes l 1 = l

/-- If the list is shorter than k, reverseKNodes returns the list unchanged. -/
def spec_revk_reverseKNodes_short_id (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (k : Nat), l.length < k →
    impl.linkedList.revk_reverseKNodes l k = l

/-- When k = l.length (and l is non-empty), the entire list is reversed. -/
def spec_revk_reverseKNodes_full (impl : RepoImpl) : Prop :=
  ∀ (l : List Int), l ≠ [] →
    impl.linkedList.revk_reverseKNodes l l.length = l.reverse

/-- reverseKNodes preserves the length of the list for all k. -/
def spec_revk_reverseKNodes_length (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (k : Nat),
    (impl.linkedList.revk_reverseKNodes l k).length = l.length

/-- General behavior: reverse every complete k-sized group and leave the remainder in order. -/
def spec_revk_reverseKNodes_chunk_model (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (k : Nat),
    impl.linkedList.revk_reverseKNodes l k = spec_helper_reverseKGroups l k
