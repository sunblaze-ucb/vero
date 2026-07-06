import LinkedList.Harness

/-!
# LinkedList.Spec.SwapNodes

Specifications for node-swapping linked list operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- swap_push prepends the element, implementing cons. -/
def spec_swap_push_cons (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int), impl.linkedList.swap_push l a = a :: l

/-- Find the index of the first occurrence of a value. -/
def spec_helper_findFirstIdx (v : Int) : List Int → Option Nat
  | [] => none
  | x :: xs =>
      if x == v then some 0
      else (spec_helper_findFirstIdx v xs).map Nat.succ

/-- Replace the value at a list index, leaving out-of-range lists unchanged. -/
def spec_helper_setAt (i : Nat) (newVal : Int) : List Int → List Int
  | [] => []
  | x :: xs =>
      if i == 0 then newVal :: xs
      else x :: spec_helper_setAt (i - 1) newVal xs

/-- Reference model: swap the first occurrences of two distinct present values. -/
def spec_helper_swapFirstOccurrences (l : List Int) (x y : Int) : List Int :=
  if x == y then l
  else
    match spec_helper_findFirstIdx x l, spec_helper_findFirstIdx y l with
    | some i, some j => spec_helper_setAt j x (spec_helper_setAt i y l)
    | _, _ => l

/-- Swapping a value with itself is a no-op. -/
def spec_swap_swapNodes_self_id (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (x : Int),
    impl.linkedList.swap_swapNodes l x x = l

/-- If either x or y is absent, swapNodes returns the list unchanged. -/
def spec_swap_swapNodes_missing_noop (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (x y : Int),
    (¬(x ∈ l) ∨ ¬(y ∈ l)) →
    impl.linkedList.swap_swapNodes l x y = l

/-- Swapping x and y twice restores the original list, when both are present,
    distinct, and each occurs exactly once. The `count = 1` guards are required:
    the swap locates the *first* occurrence of each value, so if a swapped value
    recurs the second application re-reads different first-occurrence indices and
    scrambles the list rather than restoring it (e.g. `l = [1,1,2], x = 1, y = 2`
    gives `[1,2,1]`). With each of `x` and `y` unique the first-occurrence indices
    are stable across the round trip and involution holds (duplicates of *other*
    values are still permitted). -/
def spec_swap_swapNodes_involutive (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (x y : Int),
    x ≠ y → x ∈ l → y ∈ l →
    l.count x = 1 → l.count y = 1 →
    impl.linkedList.swap_swapNodes
      (impl.linkedList.swap_swapNodes l x y) x y = l

/-- Exact behavior: swapNodes follows the first-occurrence swap model. -/
def spec_swap_swapNodes_first_occurrence_model (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (x y : Int),
    impl.linkedList.swap_swapNodes l x y =
      spec_helper_swapFirstOccurrences l x y
