-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Queues.Impl.QueueByList

FIFO queue backed by a Python list. `put` appends to the back;
`get` removes from the front; `rotate n` moves the first `n`
elements to the back; `getFront` peeks at the front element.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations.
-/

-- ── Core data type (DO NOT MODIFY) ────────────────────────────────

/-- FIFO queue backed by `List α` (front = head). -/
abbrev QueueByList (α : Type) := List α

namespace QueueByList

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────

abbrev LengthSig   := ∀ {α : Type}, QueueByList α → Nat
abbrev PutSig      := ∀ {α : Type}, QueueByList α → α → QueueByList α
abbrev GetSig      := ∀ {α : Type}, QueueByList α → Option (α × QueueByList α)
abbrev RotateSig   := ∀ {α : Type}, QueueByList α → Nat → QueueByList α
abbrev GetFrontSig := ∀ {α : Type} [Inhabited α], QueueByList α → α

end QueueByList

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Constructor ────────────────────────────────────────────────────

/-- Build a `QueueByList` from a list. -/
def QueueByList.fromList {α : Type} (l : List α) : QueueByList α := l

-- ── Implementations ────────────────────────────────────────────────

-- !benchmark @start code_aux def=length
-- !benchmark @end code_aux def=length

def QueueByList.length : QueueByList.LengthSig :=
-- !benchmark @start code def=length
  fun q => List.length q
-- !benchmark @end code def=length

-- !benchmark @start code_aux def=put
-- !benchmark @end code_aux def=put

def QueueByList.put : QueueByList.PutSig :=
-- !benchmark @start code def=put
  fun q a => q ++ [a]
-- !benchmark @end code def=put

-- !benchmark @start code_aux def=get
-- !benchmark @end code_aux def=get

def QueueByList.get : QueueByList.GetSig :=
-- !benchmark @start code def=get
  fun q =>
    match q with
    | []        => none
    | a :: rest => some (a, rest)
-- !benchmark @end code def=get

-- !benchmark @start code_aux def=rotate
-- !benchmark @end code_aux def=rotate

-- @review human: Python rotate(n) moves first n elements to back. For empty queue, no-op.
def QueueByList.rotate : QueueByList.RotateSig :=
-- !benchmark @start code def=rotate
  fun q n =>
    if q.isEmpty then q
    else
      let n' := n % List.length q
      List.drop n' q ++ List.take n' q
-- !benchmark @end code def=rotate

-- !benchmark @start code_aux def=getFront
-- !benchmark @end code_aux def=getFront

def QueueByList.getFront : QueueByList.GetFrontSig :=
-- !benchmark @start code def=getFront
  fun {α} [Inhabited α] q =>
    match q with
    | []      => default
    | a :: _ => a
-- !benchmark @end code def=getFront
