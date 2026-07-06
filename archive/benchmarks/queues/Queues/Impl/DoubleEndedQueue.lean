-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Queues.Impl.DoubleEndedQueue

Double-ended queue (deque). Supports O(1) insertions and removals at
both ends. Backed by `List α` (front-to-back); pop/popleft/appendleft
operate on the head, append/pop operate on the tail via reversal.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations.
-/

-- ── Core data type (DO NOT MODIFY) ────────────────────────────────

/-- Double-ended queue: `List α` ordered front-to-back. -/
abbrev Deque (α : Type) := List α

namespace DoubleEndedQueue

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────

abbrev IsEmptySig     := ∀ {α : Type}, Deque α → Bool
abbrev LengthSig      := ∀ {α : Type}, Deque α → Nat
abbrev AppendSig      := ∀ {α : Type}, Deque α → α → Deque α
abbrev AppendLeftSig  := ∀ {α : Type}, Deque α → α → Deque α
abbrev ExtendSig      := ∀ {α : Type}, Deque α → List α → Deque α
abbrev ExtendLeftSig  := ∀ {α : Type}, Deque α → List α → Deque α
abbrev PopSig         := ∀ {α : Type}, Deque α → Option (α × Deque α)
abbrev PopLeftSig     := ∀ {α : Type}, Deque α → Option (α × Deque α)

end DoubleEndedQueue

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Constructor ────────────────────────────────────────────────────

/-- Construct a `Deque` from a list (front-to-back). -/
def DoubleEndedQueue.fromList {α : Type} (l : List α) : Deque α := l

-- ── Implementations ────────────────────────────────────────────────

-- !benchmark @start code_aux def=isEmpty
-- !benchmark @end code_aux def=isEmpty

def DoubleEndedQueue.isEmpty : DoubleEndedQueue.IsEmptySig :=
-- !benchmark @start code def=isEmpty
  fun d => d.isEmpty
-- !benchmark @end code def=isEmpty

-- !benchmark @start code_aux def=length
-- !benchmark @end code_aux def=length

def DoubleEndedQueue.length : DoubleEndedQueue.LengthSig :=
-- !benchmark @start code def=length
  fun d => d.length
-- !benchmark @end code def=length

-- !benchmark @start code_aux def=append
-- !benchmark @end code_aux def=append

def DoubleEndedQueue.append : DoubleEndedQueue.AppendSig :=
-- !benchmark @start code def=append
  fun d a => d ++ [a]
-- !benchmark @end code def=append

-- !benchmark @start code_aux def=appendLeft
-- !benchmark @end code_aux def=appendLeft

def DoubleEndedQueue.appendLeft : DoubleEndedQueue.AppendLeftSig :=
-- !benchmark @start code def=appendLeft
  fun d a => a :: d
-- !benchmark @end code def=appendLeft

-- !benchmark @start code_aux def=extend
-- !benchmark @end code_aux def=extend

def DoubleEndedQueue.extend : DoubleEndedQueue.ExtendSig :=
-- !benchmark @start code def=extend
  fun d l => d ++ l
-- !benchmark @end code def=extend

-- !benchmark @start code_aux def=extendLeft
-- !benchmark @end code_aux def=extendLeft

-- @review human: Python extendleft prepends each element one-by-one, reversing the
-- iterable order. So extendLeft d [0, -1] on [1,2,3] gives [-1, 0, 1, 2, 3].
def DoubleEndedQueue.extendLeft : DoubleEndedQueue.ExtendLeftSig :=
-- !benchmark @start code def=extendLeft
  fun d l => l.reverse ++ d
-- !benchmark @end code def=extendLeft

-- !benchmark @start code_aux def=pop
-- !benchmark @end code_aux def=pop

def DoubleEndedQueue.pop : DoubleEndedQueue.PopSig :=
-- !benchmark @start code def=pop
  fun d =>
    match d.reverse with
    | []        => none
    | a :: rest => some (a, rest.reverse)
-- !benchmark @end code def=pop

-- !benchmark @start code_aux def=popLeft
-- !benchmark @end code_aux def=popLeft

def DoubleEndedQueue.popLeft : DoubleEndedQueue.PopLeftSig :=
-- !benchmark @start code def=popLeft
  fun d =>
    match d with
    | []        => none
    | a :: rest => some (a, rest)
-- !benchmark @end code def=popLeft
