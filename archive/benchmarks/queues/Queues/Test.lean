import Queues.Impl.CircularQueue
import Queues.Impl.CircularQueueLinkedList
import Queues.Impl.DoubleEndedQueue
import Queues.Impl.LinkedQueue
import Queues.Impl.PriorityQueueUsingList
import Queues.Impl.QueueByList
import Queues.Impl.QueueByTwoStacks
import Queues.Impl.QueueOnPseudoStack
import Queues.Bundle
import Queues.Harness

/-!
# Queues.Test

`#guard` conformance tests. Every guard invokes the API via the
bundle-qualified form `canonical.queues.<field>` so that the same
tests evaluate the LLM's filled-in implementations during grading.

Guards are kept minimal/total and avoid heavy unification: tests use
`Nat` element types and explicit calls so elaboration stays fast.

DO NOT MODIFY — infrastructure.
-/

-- ── CircularQueue ─────────────────────────────────────────────────

-- size: empty queue has size 0
#guard canonical.queues.cq_size (CircularQueue.newWithCapacity (α := Nat) 5) == 0

-- size: after one enqueue, size is 1
#guard canonical.queues.cq_size
         (canonical.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 5) 7) == 1

-- size: after two enqueues, size is 2
#guard canonical.queues.cq_size
         (canonical.queues.cq_enqueue
           (canonical.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 5) 1) 2) == 2

-- isEmpty: fresh queue is empty
#guard canonical.queues.cq_isEmpty (CircularQueue.newWithCapacity (α := Nat) 5) == true

-- isEmpty: after enqueue is not empty
#guard canonical.queues.cq_isEmpty
         (canonical.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 5) 1) == false

-- isEmpty: capacity-0 queue is empty (cannot enqueue)
#guard canonical.queues.cq_isEmpty (CircularQueue.newWithCapacity (α := Nat) 0) == true

-- first: empty queue returns default (0 for Nat)
#guard canonical.queues.cq_first (CircularQueue.newWithCapacity (α := Nat) 3) == 0

-- first: after enqueue, head is the enqueued element
#guard canonical.queues.cq_first
         (canonical.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 3) 42) == 42

-- first: FIFO — first element stays at the front
#guard canonical.queues.cq_first
         (canonical.queues.cq_enqueue
           (canonical.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 3) 9) 5) == 9

-- enqueue: into empty queue produces size-1
#guard canonical.queues.cq_size
         (canonical.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 2) 11) == 1

-- enqueue: when full, is a no-op (capacity 1, second enqueue ignored)
#guard canonical.queues.cq_size
         (canonical.queues.cq_enqueue
           (canonical.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 1) 1) 2) == 1

-- enqueue: capacity-0 queue stays empty
#guard canonical.queues.cq_isEmpty
         (canonical.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 0) 99) == true

-- dequeue: empty queue returns none
#guard (canonical.queues.cq_dequeue (CircularQueue.newWithCapacity (α := Nat) 5)) == none

-- dequeue: after one enqueue, returns that element and an empty queue
#guard (canonical.queues.cq_dequeue
         (canonical.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 5) 7)).map
         (fun p => p.fst) == some 7

-- dequeue: FIFO — returns first-enqueued element first
#guard (canonical.queues.cq_dequeue
         (canonical.queues.cq_enqueue
           (canonical.queues.cq_enqueue (CircularQueue.newWithCapacity (α := Nat) 5) 1) 2)).map
         (fun p => p.fst) == some 1

-- ── CircularQueueLinkedList ────────────────────────────────────────

-- isEmpty: fresh queue is empty
#guard canonical.queues.cqll_isEmpty (CircularQueueLinkedList.newWithCapacity (α := Nat) 6) == true

-- isEmpty: after enqueue is not empty
#guard canonical.queues.cqll_isEmpty
         (canonical.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity (α := Nat) 6) 1) == false

-- isEmpty: capacity-0 queue is empty
#guard canonical.queues.cqll_isEmpty (CircularQueueLinkedList.newWithCapacity (α := Nat) 0) == true

-- first: empty queue returns default
#guard canonical.queues.cqll_first (CircularQueueLinkedList.newWithCapacity (α := Nat) 4) == 0

-- first: after enqueue, head is the enqueued element
#guard canonical.queues.cqll_first
         (canonical.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity (α := Nat) 4) 17) == 17

-- first: FIFO — first element stays at the front
#guard canonical.queues.cqll_first
         (canonical.queues.cqll_enqueue
           (canonical.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity (α := Nat) 4) 8) 3) == 8

-- enqueue: into empty queue, isEmpty becomes false
#guard canonical.queues.cqll_isEmpty
         (canonical.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity (α := Nat) 3) 1) == false

-- enqueue: dequeue returns the enqueued element
#guard (canonical.queues.cqll_dequeue
         (canonical.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity (α := Nat) 3) 21)).map
         (fun p => p.fst) == some 21

-- enqueue: when full, is a no-op (capacity 1)
#guard (canonical.queues.cqll_dequeue
         (canonical.queues.cqll_enqueue
           (canonical.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity (α := Nat) 1) 1) 2)).map
         (fun p => p.fst) == some 1

-- dequeue: empty queue returns none
#guard (canonical.queues.cqll_dequeue (CircularQueueLinkedList.newWithCapacity (α := Nat) 6)) == none

-- dequeue: after enqueue, returns that element
#guard (canonical.queues.cqll_dequeue
         (canonical.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity (α := Nat) 6) 11)).map
         (fun p => p.fst) == some 11

-- dequeue: FIFO ordering — first-in comes out first
#guard (canonical.queues.cqll_dequeue
         (canonical.queues.cqll_enqueue
           (canonical.queues.cqll_enqueue (CircularQueueLinkedList.newWithCapacity (α := Nat) 6) 1) 2)).map
         (fun p => p.fst) == some 1

-- ── DoubleEndedQueue ──────────────────────────────────────────────

-- isEmpty: empty list
#guard canonical.queues.deque_isEmpty (DoubleEndedQueue.fromList ([] : List Nat)) == true

-- isEmpty: non-empty list
#guard canonical.queues.deque_isEmpty (DoubleEndedQueue.fromList [1, 2, 3]) == false

-- isEmpty: singleton
#guard canonical.queues.deque_isEmpty (DoubleEndedQueue.fromList [42]) == false

-- length: empty list has length 0
#guard canonical.queues.deque_length (DoubleEndedQueue.fromList ([] : List Nat)) == 0

-- length: three-element list has length 3
#guard canonical.queues.deque_length (DoubleEndedQueue.fromList [1, 2, 3]) == 3

-- length: singleton list has length 1
#guard canonical.queues.deque_length (DoubleEndedQueue.fromList [99]) == 1

-- append: into empty produces singleton
#guard canonical.queues.deque_append (DoubleEndedQueue.fromList ([] : List Nat)) 5
         == DoubleEndedQueue.fromList [5]

-- append: appends to the right
#guard canonical.queues.deque_append (DoubleEndedQueue.fromList [1, 2]) 3
         == DoubleEndedQueue.fromList [1, 2, 3]

-- append: increases length by 1
#guard canonical.queues.deque_length
         (canonical.queues.deque_append (DoubleEndedQueue.fromList [1, 2]) 3) == 3

-- appendLeft: into empty produces singleton
#guard canonical.queues.deque_appendLeft (DoubleEndedQueue.fromList ([] : List Nat)) 5
         == DoubleEndedQueue.fromList [5]

-- appendLeft: prepends to the left
#guard canonical.queues.deque_appendLeft (DoubleEndedQueue.fromList [2, 3]) 1
         == DoubleEndedQueue.fromList [1, 2, 3]

-- appendLeft: increases length by 1
#guard canonical.queues.deque_length
         (canonical.queues.deque_appendLeft (DoubleEndedQueue.fromList [2, 3]) 1) == 3

-- extend: empty extension is a no-op
#guard canonical.queues.deque_extend (DoubleEndedQueue.fromList [1, 2]) ([] : List Nat)
         == DoubleEndedQueue.fromList [1, 2]

-- extend: appends list to the right
#guard canonical.queues.deque_extend (DoubleEndedQueue.fromList [1, 2]) [3, 4]
         == DoubleEndedQueue.fromList [1, 2, 3, 4]

-- extend: extending empty by xs gives xs
#guard canonical.queues.deque_extend (DoubleEndedQueue.fromList ([] : List Nat)) [7, 8, 9]
         == DoubleEndedQueue.fromList [7, 8, 9]

-- extendLeft: empty extension is a no-op
#guard canonical.queues.deque_extendLeft (DoubleEndedQueue.fromList [1, 2]) ([] : List Nat)
         == DoubleEndedQueue.fromList [1, 2]

-- extendLeft: prepends list reversed (Python semantics)
#guard canonical.queues.deque_extendLeft (DoubleEndedQueue.fromList [1, 2, 3]) [0, 5]
         == DoubleEndedQueue.fromList [5, 0, 1, 2, 3]

-- extendLeft: extending empty by xs gives xs reversed
#guard canonical.queues.deque_extendLeft (DoubleEndedQueue.fromList ([] : List Nat)) [1, 2, 3]
         == DoubleEndedQueue.fromList [3, 2, 1]

-- pop: empty deque returns none
#guard (canonical.queues.deque_pop (DoubleEndedQueue.fromList ([] : List Nat))) == none

-- pop: removes from the right
#guard canonical.queues.deque_pop (DoubleEndedQueue.fromList [1, 2, 3])
         == some (3, DoubleEndedQueue.fromList [1, 2])

-- pop: singleton becomes empty
#guard canonical.queues.deque_pop (DoubleEndedQueue.fromList [42])
         == some (42, DoubleEndedQueue.fromList ([] : List Nat))

-- popLeft: empty deque returns none
#guard (canonical.queues.deque_popLeft (DoubleEndedQueue.fromList ([] : List Nat))) == none

-- popLeft: removes from the left
#guard canonical.queues.deque_popLeft (DoubleEndedQueue.fromList [1, 2, 3])
         == some (1, DoubleEndedQueue.fromList [2, 3])

-- popLeft: singleton becomes empty
#guard canonical.queues.deque_popLeft (DoubleEndedQueue.fromList [42])
         == some (42, DoubleEndedQueue.fromList ([] : List Nat))

-- ── LinkedQueue ───────────────────────────────────────────────────

-- length: empty queue
#guard canonical.queues.lq_length (LinkedQueue.fromList ([] : List Nat)) == 0

-- length: five-element queue
#guard canonical.queues.lq_length (LinkedQueue.fromList [1, 2, 3, 4, 5]) == 5

-- length: singleton queue
#guard canonical.queues.lq_length (LinkedQueue.fromList [7]) == 1

-- isEmpty: empty queue
#guard canonical.queues.lq_isEmpty (LinkedQueue.fromList ([] : List Nat)) == true

-- isEmpty: singleton queue
#guard canonical.queues.lq_isEmpty (LinkedQueue.fromList [1]) == false

-- isEmpty: multi-element queue
#guard canonical.queues.lq_isEmpty (LinkedQueue.fromList [1, 2, 3]) == false

-- put: into empty queue
#guard canonical.queues.lq_put (LinkedQueue.fromList ([] : List Nat)) 5
         == LinkedQueue.fromList [5]

-- put: appends to the back
#guard canonical.queues.lq_put (LinkedQueue.fromList [1, 2]) 3
         == LinkedQueue.fromList [1, 2, 3]

-- put: increases length by 1
#guard canonical.queues.lq_length (canonical.queues.lq_put (LinkedQueue.fromList [1, 2]) 3) == 3

-- get: empty queue returns none
#guard (canonical.queues.lq_get (LinkedQueue.fromList ([] : List Nat))) == none

-- get: returns front element and remainder
#guard canonical.queues.lq_get (LinkedQueue.fromList [1, 2, 3])
         == some (1, LinkedQueue.fromList [2, 3])

-- get: singleton becomes empty
#guard canonical.queues.lq_get (LinkedQueue.fromList [42])
         == some (42, LinkedQueue.fromList ([] : List Nat))

-- clear: of empty queue is empty
#guard canonical.queues.lq_clear (LinkedQueue.fromList ([] : List Nat))
         == LinkedQueue.fromList ([] : List Nat)

-- clear: drops all elements
#guard canonical.queues.lq_clear (LinkedQueue.fromList [1, 2, 3, 4, 5])
         == LinkedQueue.fromList ([] : List Nat)

-- clear: result has length 0
#guard canonical.queues.lq_length (canonical.queues.lq_clear (LinkedQueue.fromList [1, 2, 3])) == 0

-- ── PriorityQueueUsingList ────────────────────────────────────────

-- fpq_enqueue: dequeue after enqueueing at priority 0 returns that element
#guard (canonical.queues.fpq_dequeue
         (canonical.queues.fpq_enqueue (FixedPriorityQueue.new (α := Nat)) 0 10)).map
         (fun p => p.fst) == some 10

-- fpq_enqueue: priority 1 vs priority 2 — priority 1 dequeues first
#guard (canonical.queues.fpq_dequeue
         (canonical.queues.fpq_enqueue
           (canonical.queues.fpq_enqueue (FixedPriorityQueue.new (α := Nat)) 2 99) 1 7)).map
         (fun p => p.fst) == some 7

-- fpq_enqueue: invalid priority is a no-op (queue stays empty)
#guard (canonical.queues.fpq_dequeue
         (canonical.queues.fpq_enqueue (FixedPriorityQueue.new (α := Nat)) 5 100)) == none

-- fpq_dequeue: empty queue returns none
#guard (canonical.queues.fpq_dequeue (FixedPriorityQueue.new (α := Nat))) == none

-- fpq_dequeue: highest priority dequeues before lower
#guard (canonical.queues.fpq_dequeue
         (canonical.queues.fpq_enqueue
           (canonical.queues.fpq_enqueue (FixedPriorityQueue.new (α := Nat)) 2 99) 0 1)).map
         (fun p => p.fst) == some 1

-- fpq_dequeue: from a queue with only priority 2 returns that element
#guard (canonical.queues.fpq_dequeue
         (canonical.queues.fpq_enqueue (FixedPriorityQueue.new (α := Nat)) 2 42)).map
         (fun p => p.fst) == some 42

-- epq_enqueue: enqueue then dequeue gives same element
#guard (canonical.queues.epq_dequeue
         (canonical.queues.epq_enqueue (ElementPriorityQueue.new (α := Nat)) 10)).map
         (fun p => p.fst) == some 10

-- epq_enqueue: minimum element dequeues first
#guard (canonical.queues.epq_dequeue
         (canonical.queues.epq_enqueue
           (canonical.queues.epq_enqueue (ElementPriorityQueue.new (α := Nat)) 5) 3)).map
         (fun p => p.fst) == some 3

-- epq_enqueue: dequeueing leaves the rest behind
#guard (canonical.queues.epq_dequeue
         (canonical.queues.epq_enqueue
           (canonical.queues.epq_enqueue (ElementPriorityQueue.new (α := Nat)) 7) 9)).map
         (fun p => p.fst) == some 7

-- epq_dequeue: empty returns none
#guard (canonical.queues.epq_dequeue (ElementPriorityQueue.new (α := Nat))) == none

-- epq_dequeue: returns minimum
#guard (canonical.queues.epq_dequeue
         (canonical.queues.epq_enqueue
           (canonical.queues.epq_enqueue
             (canonical.queues.epq_enqueue (ElementPriorityQueue.new (α := Nat)) 4) 1) 8)).map
         (fun p => p.fst) == some 1

-- epq_dequeue: singleton returns that element
#guard (canonical.queues.epq_dequeue
         (canonical.queues.epq_enqueue (ElementPriorityQueue.new (α := Nat)) 42)).map
         (fun p => p.fst) == some 42

-- ── QueueByList ───────────────────────────────────────────────────

-- length: empty queue
#guard canonical.queues.qbl_length (QueueByList.fromList ([] : List Nat)) == 0

-- length: three-element queue
#guard canonical.queues.qbl_length (QueueByList.fromList [10, 20, 30]) == 3

-- length: singleton queue
#guard canonical.queues.qbl_length (QueueByList.fromList [99]) == 1

-- put: into empty produces singleton
#guard canonical.queues.qbl_put (QueueByList.fromList ([] : List Nat)) 5
         == QueueByList.fromList [5]

-- put: appends to the back
#guard canonical.queues.qbl_put (QueueByList.fromList [1, 2]) 3
         == QueueByList.fromList [1, 2, 3]

-- put: increases length by 1
#guard canonical.queues.qbl_length (canonical.queues.qbl_put (QueueByList.fromList [1, 2]) 3) == 3

-- get: returns front element
#guard canonical.queues.qbl_get (QueueByList.fromList [10, 20, 30])
         == some (10, QueueByList.fromList [20, 30])

-- get: empty queue returns none
#guard (canonical.queues.qbl_get (QueueByList.fromList ([] : List Nat))) == none

-- get: singleton becomes empty
#guard canonical.queues.qbl_get (QueueByList.fromList [42])
         == some (42, QueueByList.fromList ([] : List Nat))

-- rotate: empty queue is unchanged
#guard canonical.queues.qbl_rotate (QueueByList.fromList ([] : List Nat)) 3
         == QueueByList.fromList ([] : List Nat)

-- rotate: by 1 moves first element to back
#guard canonical.queues.qbl_rotate (QueueByList.fromList [1, 2, 3]) 1
         == QueueByList.fromList [2, 3, 1]

-- rotate: by length is identity
#guard canonical.queues.qbl_rotate (QueueByList.fromList [1, 2, 3]) 3
         == QueueByList.fromList [1, 2, 3]

-- getFront: empty queue returns default
#guard canonical.queues.qbl_getFront (QueueByList.fromList ([] : List Nat)) == 0

-- getFront: returns the first element
#guard canonical.queues.qbl_getFront (QueueByList.fromList [10, 20, 30]) == 10

-- getFront: singleton returns its only element
#guard canonical.queues.qbl_getFront (QueueByList.fromList [42]) == 42

-- ── QueueByTwoStacks ──────────────────────────────────────────────

-- length: empty queue
#guard canonical.queues.qbts_length (QueueByTwoStacks.fromList ([] : List Nat)) == 0

-- length: three-element queue
#guard canonical.queues.qbts_length (QueueByTwoStacks.fromList [10, 20, 30]) == 3

-- length: singleton queue
#guard canonical.queues.qbts_length (QueueByTwoStacks.fromList [7]) == 1

-- put: into empty produces singleton
#guard canonical.queues.qbts_put (QueueByTwoStacks.fromList ([] : List Nat)) 5
         == QueueByTwoStacks.fromList [5]

-- put: appends to the back
#guard canonical.queues.qbts_put (QueueByTwoStacks.fromList [1, 2]) 3
         == QueueByTwoStacks.fromList [1, 2, 3]

-- put: increases length by 1
#guard canonical.queues.qbts_length
         (canonical.queues.qbts_put (QueueByTwoStacks.fromList [1, 2]) 3) == 3

-- get: returns the front element
#guard canonical.queues.qbts_get (QueueByTwoStacks.fromList [10, 20, 30])
         == some (10, QueueByTwoStacks.fromList [20, 30])

-- get: empty queue returns none
#guard (canonical.queues.qbts_get (QueueByTwoStacks.fromList ([] : List Nat))) == none

-- get: singleton becomes empty
#guard canonical.queues.qbts_get (QueueByTwoStacks.fromList [42])
         == some (42, QueueByTwoStacks.fromList ([] : List Nat))

-- ── QueueOnPseudoStack ────────────────────────────────────────────

-- put: into empty produces singleton
#guard canonical.queues.qops_put (QueueOnPseudoStack.fromList ([] : List Nat)) 5
         == QueueOnPseudoStack.fromList [5]

-- put: appends to the back
#guard canonical.queues.qops_put (QueueOnPseudoStack.fromList [1, 2]) 3
         == QueueOnPseudoStack.fromList [1, 2, 3]

-- put: increases size by 1
#guard canonical.queues.qops_size
         (canonical.queues.qops_put (QueueOnPseudoStack.fromList [1, 2]) 3) == 3

-- get: returns the front element
#guard canonical.queues.qops_get (QueueOnPseudoStack.fromList [10, 20, 30])
         == some (10, QueueOnPseudoStack.fromList [20, 30])

-- get: empty queue returns none
#guard (canonical.queues.qops_get (QueueOnPseudoStack.fromList ([] : List Nat))) == none

-- get: singleton becomes empty
#guard canonical.queues.qops_get (QueueOnPseudoStack.fromList [42])
         == some (42, QueueOnPseudoStack.fromList ([] : List Nat))

-- rotate: empty queue is unchanged
#guard canonical.queues.qops_rotate (QueueOnPseudoStack.fromList ([] : List Nat)) 2
         == QueueOnPseudoStack.fromList ([] : List Nat)

-- rotate: by 1 moves first element to back
#guard canonical.queues.qops_rotate (QueueOnPseudoStack.fromList [1, 2, 3]) 1
         == QueueOnPseudoStack.fromList [2, 3, 1]

-- rotate: by length is identity
#guard canonical.queues.qops_rotate (QueueOnPseudoStack.fromList [1, 2, 3]) 3
         == QueueOnPseudoStack.fromList [1, 2, 3]

-- front: empty queue returns default
#guard canonical.queues.qops_front (QueueOnPseudoStack.fromList ([] : List Nat)) == 0

-- front: returns the first element
#guard canonical.queues.qops_front (QueueOnPseudoStack.fromList [10, 20, 30]) == 10

-- front: singleton returns its only element
#guard canonical.queues.qops_front (QueueOnPseudoStack.fromList [42]) == 42

-- size: empty queue
#guard canonical.queues.qops_size (QueueOnPseudoStack.fromList ([] : List Nat)) == 0

-- size: three-element queue
#guard canonical.queues.qops_size (QueueOnPseudoStack.fromList [10, 20, 30]) == 3

-- size: singleton queue
#guard canonical.queues.qops_size (QueueOnPseudoStack.fromList [7]) == 1
