-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Queues.Impl.QueueByTwoStacks

FIFO queue implemented with two stacks in Python. The Lean
translation abstracts over the internal two-stack representation
and uses `List α` (front = head) as the canonical backing store.
All operations preserve the FIFO invariant.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations.
-/

-- ── Core data type (DO NOT MODIFY) ────────────────────────────────

/-- FIFO queue implemented via two stacks in Python; Lean uses `List α` directly.
    @review human: two-stack representation abstracted to List α for functional purity. -/
abbrev QueueByTwoStacks (α : Type) := List α

namespace QueueByTwoStacks

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────

abbrev LengthSig := ∀ {α : Type}, QueueByTwoStacks α → Nat
abbrev PutSig    := ∀ {α : Type}, QueueByTwoStacks α → α → QueueByTwoStacks α
abbrev GetSig    := ∀ {α : Type}, QueueByTwoStacks α → Option (α × QueueByTwoStacks α)

end QueueByTwoStacks

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Constructor ────────────────────────────────────────────────────

/-- Build a `QueueByTwoStacks` from a list. -/
def QueueByTwoStacks.fromList {α : Type} (l : List α) : QueueByTwoStacks α := l

-- ── Implementations ────────────────────────────────────────────────

-- !benchmark @start code_aux def=length
-- !benchmark @end code_aux def=length

def QueueByTwoStacks.length : QueueByTwoStacks.LengthSig :=
-- !benchmark @start code def=length
  fun q => List.length q
-- !benchmark @end code def=length

-- !benchmark @start code_aux def=put
-- !benchmark @end code_aux def=put

def QueueByTwoStacks.put : QueueByTwoStacks.PutSig :=
-- !benchmark @start code def=put
  fun q a => q ++ [a]
-- !benchmark @end code def=put

-- !benchmark @start code_aux def=get
-- !benchmark @end code_aux def=get

def QueueByTwoStacks.get : QueueByTwoStacks.GetSig :=
-- !benchmark @start code def=get
  fun q =>
    match q with
    | []        => none
    | a :: rest => some (a, rest)
-- !benchmark @end code def=get
