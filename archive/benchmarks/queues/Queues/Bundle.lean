import Queues.Impl.CircularQueue
import Queues.Impl.CircularQueueLinkedList
import Queues.Impl.DoubleEndedQueue
import Queues.Impl.LinkedQueue
import Queues.Impl.PriorityQueueUsingList
import Queues.Impl.QueueByList
import Queues.Impl.QueueByTwoStacks
import Queues.Impl.QueueOnPseudoStack

/-!
# Queues.Bundle

Per-package implementation bundle for the `Queues` root package.
Collects all 39 API signatures into one structure, one field per API.
Field names use a short prefix to disambiguate duplicate API names
across modules (e.g. `cq_size` for `CircularQueue.size`).

DO NOT MODIFY — benchmark infrastructure.
-/

structure QueuesBundle where
  -- ── CircularQueue (5 APIs) ───────────────────────────────────────
  cq_size       : CircularQueue.SizeSig
  cq_isEmpty    : CircularQueue.IsEmptySig
  cq_first      : CircularQueue.FirstSig
  cq_enqueue    : CircularQueue.EnqueueSig
  cq_dequeue    : CircularQueue.DequeueSig
  -- ── CircularQueueLinkedList (4 APIs) ─────────────────────────────
  cqll_isEmpty  : CircularQueueLinkedList.IsEmptySig
  cqll_first    : CircularQueueLinkedList.FirstSig
  cqll_enqueue  : CircularQueueLinkedList.EnqueueSig
  cqll_dequeue  : CircularQueueLinkedList.DequeueSig
  -- ── DoubleEndedQueue (8 APIs) ────────────────────────────────────
  deque_isEmpty     : DoubleEndedQueue.IsEmptySig
  deque_length      : DoubleEndedQueue.LengthSig
  deque_append      : DoubleEndedQueue.AppendSig
  deque_appendLeft  : DoubleEndedQueue.AppendLeftSig
  deque_extend      : DoubleEndedQueue.ExtendSig
  deque_extendLeft  : DoubleEndedQueue.ExtendLeftSig
  deque_pop         : DoubleEndedQueue.PopSig
  deque_popLeft     : DoubleEndedQueue.PopLeftSig
  -- ── LinkedQueue (5 APIs) ─────────────────────────────────────────
  lq_length  : LinkedQueue.LengthSig
  lq_isEmpty : LinkedQueue.IsEmptySig
  lq_put     : LinkedQueue.PutSig
  lq_get     : LinkedQueue.GetSig
  lq_clear   : LinkedQueue.ClearSig
  -- ── PriorityQueueUsingList (4 APIs) ──────────────────────────────
  fpq_enqueue  : PriorityQueueUsingList.FpqEnqueueSig
  fpq_dequeue  : PriorityQueueUsingList.FpqDequeueSig
  epq_enqueue  : PriorityQueueUsingList.EpqEnqueueSig
  epq_dequeue  : PriorityQueueUsingList.EpqDequeueSig
  -- ── QueueByList (5 APIs) ─────────────────────────────────────────
  qbl_length   : QueueByList.LengthSig
  qbl_put      : QueueByList.PutSig
  qbl_get      : QueueByList.GetSig
  qbl_rotate   : QueueByList.RotateSig
  qbl_getFront : QueueByList.GetFrontSig
  -- ── QueueByTwoStacks (3 APIs) ────────────────────────────────────
  qbts_length : QueueByTwoStacks.LengthSig
  qbts_put    : QueueByTwoStacks.PutSig
  qbts_get    : QueueByTwoStacks.GetSig
  -- ── QueueOnPseudoStack (5 APIs) ──────────────────────────────────
  qops_put    : QueueOnPseudoStack.PutSig
  qops_get    : QueueOnPseudoStack.GetSig
  qops_rotate : QueueOnPseudoStack.RotateSig
  qops_front  : QueueOnPseudoStack.FrontSig
  qops_size   : QueueOnPseudoStack.SizeSig
