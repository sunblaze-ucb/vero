import Stack.Harness
import Stack.Spec.Aux

/-!
# Stack.Spec.Stack

Specifications for the core stack ADT: `isEmpty`, `size`, `isFull`,
`peek`, `pop`, `contains`, and `fromList`.

The key convention: `Stack α` is `List α`; `peek`/`pop` observe the head,
while `push x s = s ++ [x]` appends at the tail. Laws below use `fromList`
for the public constructor-style round trips, since `fromList` reverses a
source list into head-as-top stack order.

DO NOT MODIFY — frozen curator-given content.
-/

/-- The distinguished empty stack is empty, has size zero, and has no top or popped element. -/
def spec_empty_stack_law (impl : RepoImpl) : Prop :=
  impl.stack.isEmpty (Stack.empty : Stack Nat) = true ∧
  impl.stack.size (Stack.empty : Stack Nat) = 0 ∧
  impl.stack.peek (Stack.empty : Stack Nat) = none ∧
  impl.stack.pop (Stack.empty : Stack Nat) = none ∧
  ∀ x : Nat, impl.stack.contains x (Stack.empty : Stack Nat) = false

/-- `isEmpty` returns `true` iff `size` returns `0`. -/
def spec_isEmpty_iff_size_zero (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (s : Stack α),
    impl.stack.isEmpty s = true ↔ impl.stack.size s = 0

/-- Pushing any natural number grows size, makes the stack non-empty, and makes the value a member. -/
def spec_push_shape_and_membership (impl : RepoImpl) : Prop :=
  ∀ (x : Nat) (s : Stack Nat),
    impl.stack.size (Stack.push x s) = impl.stack.size s + 1 ∧
    impl.stack.isEmpty (Stack.push x s) = false ∧
    impl.stack.contains x (Stack.push x s) = true

/-- Converting a list to a stack preserves length and agrees with list emptiness. -/
def spec_fromList_shape (impl : RepoImpl) : Prop :=
  ∀ (l : List Nat),
    impl.stack.size (impl.stack.fromList l) = l.length ∧
    impl.stack.isEmpty (impl.stack.fromList l) =
      match l with
      | [] => true
      | _ :: _ => false

/-- `isFull s n` is `true` exactly when the size has reached or exceeded capacity `n`. -/
def spec_isFull_threshold (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (s : Stack α) (n : Nat),
    impl.stack.isFull s n = true ↔ impl.stack.size s ≥ n

/-- The element returned by `pop` agrees with `peek`. -/
def spec_pop_peek_agree (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (s : Stack α),
    (impl.stack.pop s).map Prod.fst = impl.stack.peek s

/-- Pushing a different natural number does not affect membership of `x`. -/
def spec_contains_after_push_other (impl : RepoImpl) : Prop :=
  ∀ (x y : Nat) (s : Stack Nat),
    x ≠ y →
    impl.stack.contains x (Stack.push y s) = impl.stack.contains x s

/-- Membership in a stack built from a list is exactly list membership. -/
def spec_contains_fromList_iff_mem (impl : RepoImpl) : Prop :=
  ∀ (x : Nat) (xs : List Nat),
    impl.stack.contains x (impl.stack.fromList xs) = decide (x ∈ xs)

/-- The observable top of `fromList xs` is the last element of `xs`. -/
def spec_fromList_top_matches_last (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (xs : List α),
    impl.stack.peek (impl.stack.fromList xs) = listLast? xs

/-- Popping after appending one source-list element recovers that element and the prior `fromList` stack. -/
def spec_pop_fromList_append_singleton (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (xs : List α) (x : α),
    impl.stack.pop (impl.stack.fromList (xs ++ [x])) = some (x, impl.stack.fromList xs)

/-- Pushing `x` onto the empty stack and peeking returns `some x`. -/
def spec_peek_after_push_empty (impl : RepoImpl) : Prop :=
  ∀ x : Nat,
    impl.stack.peek (Stack.push x Stack.empty) = some x

/-- Pushing onto a non-empty stack does not change the top element.
    Uses the two-layer form to guarantee the inner stack is non-empty
    without an explicit `s ≠ []` hypothesis. -/
def spec_peek_after_push_nonempty (impl : RepoImpl) : Prop :=
  ∀ (x y : Nat) (s : Stack Nat),
    impl.stack.peek (Stack.push x (Stack.push y s)) =
    impl.stack.peek (Stack.push y s)

/-- Popping from a singleton stack (push x onto empty) returns `some (x, empty)`. -/
def spec_pop_singleton (impl : RepoImpl) : Prop :=
  ∀ x : Nat,
    impl.stack.pop (Stack.push x Stack.empty) = some (x, Stack.empty)

/-- Converting the empty list gives the empty stack. -/
def spec_fromList_empty (impl : RepoImpl) : Prop :=
  impl.stack.fromList ([] : List Nat) = (Stack.empty : Stack Nat)

/-- `fromList [x]` equals `push x empty`. -/
def spec_fromList_singleton (impl : RepoImpl) : Prop :=
  ∀ x : Nat,
    impl.stack.fromList [x] = Stack.push x Stack.empty

/-- `fromList` is an involution: `fromList ∘ fromList = id`. -/
def spec_fromList_involutive (impl : RepoImpl) : Prop :=
  ∀ l : List Nat,
    impl.stack.fromList (impl.stack.fromList l) = l

/-- Polymorphic empty-stack law (ported from PR-#35 `EmptyStackLaw`):
    for every element type `α`, the distinguished empty stack has size zero
    and reports itself as empty. The earlier `spec_empty_stack_law` pins
    these observers only at `α = Nat`; this variant strengthens them to all
    types without committing to peek/pop/contains observations. -/
def spec_empty_stack_law_all_types (impl : RepoImpl) : Prop :=
  ∀ {α : Type},
    impl.stack.size (Stack.empty : Stack α) = 0 ∧
    impl.stack.isEmpty (Stack.empty : Stack α) = true
