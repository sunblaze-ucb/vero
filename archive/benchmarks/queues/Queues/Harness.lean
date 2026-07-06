import Queues.Bundle

/-!
# Queues.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring all 39 APIs, and the `joint_unsat` macro.

DO NOT MODIFY — benchmark infrastructure.
-/

-- ── Implementation bundle (one field per package) ────────────────

structure RepoImpl where
  queues : QueuesBundle

-- ── Canonical instance ───────────────────────────────────────────

def canonical : RepoImpl where
  queues := {
    -- CircularQueue
    cq_size       := CircularQueue.size
    cq_isEmpty    := CircularQueue.isEmpty
    cq_first      := CircularQueue.first
    cq_enqueue    := CircularQueue.enqueue
    cq_dequeue    := CircularQueue.dequeue
    -- CircularQueueLinkedList
    cqll_isEmpty  := CircularQueueLinkedList.isEmpty
    cqll_first    := CircularQueueLinkedList.first
    cqll_enqueue  := CircularQueueLinkedList.enqueue
    cqll_dequeue  := CircularQueueLinkedList.dequeue
    -- DoubleEndedQueue
    deque_isEmpty     := DoubleEndedQueue.isEmpty
    deque_length      := DoubleEndedQueue.length
    deque_append      := DoubleEndedQueue.append
    deque_appendLeft  := DoubleEndedQueue.appendLeft
    deque_extend      := DoubleEndedQueue.extend
    deque_extendLeft  := DoubleEndedQueue.extendLeft
    deque_pop         := DoubleEndedQueue.pop
    deque_popLeft     := DoubleEndedQueue.popLeft
    -- LinkedQueue
    lq_length  := LinkedQueue.length
    lq_isEmpty := LinkedQueue.isEmpty
    lq_put     := LinkedQueue.put
    lq_get     := LinkedQueue.get
    lq_clear   := LinkedQueue.clear
    -- PriorityQueueUsingList
    fpq_enqueue  := PriorityQueueUsingList.fpq_enqueue
    fpq_dequeue  := PriorityQueueUsingList.fpq_dequeue
    epq_enqueue  := PriorityQueueUsingList.epq_enqueue
    epq_dequeue  := PriorityQueueUsingList.epq_dequeue
    -- QueueByList
    qbl_length   := QueueByList.length
    qbl_put      := QueueByList.put
    qbl_get      := QueueByList.get
    qbl_rotate   := QueueByList.rotate
    qbl_getFront := QueueByList.getFront
    -- QueueByTwoStacks
    qbts_length := QueueByTwoStacks.length
    qbts_put    := QueueByTwoStacks.put
    qbts_get    := QueueByTwoStacks.get
    -- QueueOnPseudoStack
    qops_put    := QueueOnPseudoStack.put
    qops_get    := QueueOnPseudoStack.get
    qops_rotate := QueueOnPseudoStack.rotate
    qops_front  := QueueOnPseudoStack.front
    qops_size   := QueueOnPseudoStack.size
  }

-- ── joint_unsat macro ────────────────────────────────────────────

/--
`joint_unsat spec_A spec_B [spec_C …] by <proof>` generates
```
theorem joint_unsat.spec_A.spec_B.… :
    ¬ ∃ impl : RepoImpl, spec_A impl ∧ spec_B impl ∧ … := by <proof>
```
-/
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
