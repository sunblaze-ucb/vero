-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Queues.Impl.QueueOnPseudoStack

FIFO queue represented by a pseudo-stack (Python list used with
append/pop and rotate). The functional Lean translation uses `List α`
(front = head). `get` dequeues from the front; `rotate n` moves the
first `n` elements to the back; `front` peeks at the head element;
`size` returns the length.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations.
-/

-- ── Core data type (DO NOT MODIFY) ────────────────────────────────

/-- FIFO queue backed by a pseudo-stack; Lean uses `List α` directly. -/
abbrev Queue (α : Type) := List α

namespace QueueOnPseudoStack

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────

abbrev PutSig    := ∀ {α : Type}, Queue α → α → Queue α
abbrev GetSig    := ∀ {α : Type}, Queue α → Option (α × Queue α)
abbrev RotateSig := ∀ {α : Type}, Queue α → Nat → Queue α
/-- `front` requires `Inhabited α` to return `default` on an empty queue.
    @review human: benchmark.json sig has no Inhabited constraint; added for implementability.
    Python precondition |length| > 0 not enforced by the type. -/
abbrev FrontSig  := ∀ {α : Type} [Inhabited α], Queue α → α
abbrev SizeSig   := ∀ {α : Type}, Queue α → Nat

end QueueOnPseudoStack

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Constructor ────────────────────────────────────────────────────

/-- Build a `Queue` from a list. -/
def QueueOnPseudoStack.fromList {α : Type} (l : List α) : Queue α := l

-- ── Implementations ────────────────────────────────────────────────

-- !benchmark @start code_aux def=put
-- !benchmark @end code_aux def=put

def QueueOnPseudoStack.put : QueueOnPseudoStack.PutSig :=
-- !benchmark @start code def=put
  fun q a => q ++ [a]
-- !benchmark @end code def=put

-- !benchmark @start code_aux def=get
-- !benchmark @end code_aux def=get

def QueueOnPseudoStack.get : QueueOnPseudoStack.GetSig :=
-- !benchmark @start code def=get
  fun q =>
    match q with
    | []        => none
    | a :: rest => some (a, rest)
-- !benchmark @end code def=get

-- !benchmark @start code_aux def=rotate
-- !benchmark @end code_aux def=rotate

def QueueOnPseudoStack.rotate : QueueOnPseudoStack.RotateSig :=
-- !benchmark @start code def=rotate
  fun q n =>
    if q.isEmpty then q
    else
      let n' := n % List.length q
      List.drop n' q ++ List.take n' q
-- !benchmark @end code def=rotate

-- !benchmark @start code_aux def=front
-- !benchmark @end code_aux def=front

-- @review human: Python precondition |length| > 0; Lean returns `default` on empty queue.
def QueueOnPseudoStack.front : QueueOnPseudoStack.FrontSig :=
-- !benchmark @start code def=front
  fun {α} [Inhabited α] q =>
    match q with
    | a :: _ => a
    | []     => default
-- !benchmark @end code def=front

-- !benchmark @start code_aux def=size
-- !benchmark @end code_aux def=size

def QueueOnPseudoStack.size : QueueOnPseudoStack.SizeSig :=
-- !benchmark @start code def=size
  fun q => List.length q
-- !benchmark @end code def=size
