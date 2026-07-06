import LinkedList.Impl.SinglyLinkedList
import LinkedList.Impl.FromSequence
import LinkedList.Impl.DoublyLinkedList
import LinkedList.Impl.CircularLinkedList
import LinkedList.Impl.DequeDoubly
import LinkedList.Impl.MiddleElementOfLinkedList
import LinkedList.Impl.LinkedListInit
import LinkedList.Impl.SkipList
import LinkedList.Impl.SwapNodes
import LinkedList.Impl.DoublyLinkedListTwo
import LinkedList.Impl.MergeTwoLists
import LinkedList.Impl.ReverseKGroup
import LinkedList.Impl.HasLoop
import LinkedList.Impl.RotateToTheRight
import LinkedList.Impl.FloydsCycleDetection
import LinkedList.Impl.IsPalindrome
import LinkedList.Impl.PrintReverse

/-!
# LinkedList.Bundle

Per-package implementation bundle for the `LinkedList` root package.
Collects all API function types into one structure. Generic modules are
specialized to `Int` so that the bundle fields have concrete (non-polymorphic)
types that Lean can elaborate without synthesizing implicit type arguments.

DO NOT MODIFY — benchmark infrastructure.
-/

structure LinkedListBundle where
  -- ── SinglyLinkedList (specialized to Int) ─────────────────────
  sll_insertHead  : List Int → Int → List Int
  sll_insertTail  : List Int → Int → List Int
  sll_insertNth   : List Int → Nat → Int → List Int
  sll_deleteHead  : List Int → Option (Int × List Int)
  sll_deleteTail  : List Int → Option (Int × List Int)
  sll_deleteNth   : List Int → Nat → Option (Int × List Int)
  sll_isEmpty     : List Int → Bool
  sll_reverse     : List Int → List Int
  -- ── FromSequence (specialized to Int) ─────────────────────────
  fromSeq_makeLinkedList : List Int → Option (List Int)
  -- ── DoublyLinkedList (specialized to Int) ─────────────────────
  dll_insertAtHead : List Int → Int → List Int
  dll_insertAtTail : List Int → Int → List Int
  dll_insertAtNth  : List Int → Nat → Int → List Int
  dll_deleteHead   : List Int → Option (Int × List Int)
  dll_deleteTail   : List Int → Option (Int × List Int)
  dll_deleteAtNth  : List Int → Nat → Option (Int × List Int)
  dll_deleteData   : List Int → Int → Option (Int × List Int)
  dll_isEmpty      : List Int → Bool
  -- ── CircularLinkedList (specialized to Int) ───────────────────
  cll_insertHead  : List Int → Int → List Int
  cll_insertTail  : List Int → Int → List Int
  cll_insertNth   : List Int → Nat → Int → List Int
  cll_deleteFront : List Int → Option (Int × List Int)
  cll_deleteTail  : List Int → Option (Int × List Int)
  cll_deleteNth   : List Int → Nat → Option (Int × List Int)
  cll_isEmpty     : List Int → Bool
  -- ── DequeDoubly (specialized to Int) ──────────────────────────
  deque_first       : List Int → Option Int
  deque_last        : List Int → Option Int
  deque_addFirst    : List Int → Int → List Int
  deque_addLast     : List Int → Int → List Int
  deque_removeFirst : List Int → Option (Int × List Int)
  deque_removeLast  : List Int → Option (Int × List Int)
  deque_isEmpty     : List Int → Bool
  -- ── MiddleElementOfLinkedList (specialized to Int) ────────────
  midll_push          : List Int → Int → List Int
  midll_middleElement : List Int → Option Int
  -- ── LinkedListInit (specialized to Int) ───────────────────────
  lli_add     : List Int → Int → Nat → List Int
  lli_remove  : List Int → Option (Int × List Int)
  lli_isEmpty : List Int → Bool
  lli_length  : List Int → Nat
  -- ── SkipList (specialized to Int keys and Int values) ─────────
  skipl_insert : List (Int × Int) → Int → Int → List (Int × Int)
  skipl_delete : List (Int × Int) → Int → List (Int × Int)
  skipl_find   : List (Int × Int) → Int → Option Int
  -- ── SwapNodes (specialized to Int) ────────────────────────────
  swap_push      : List Int → Int → List Int
  swap_swapNodes : List Int → Int → Int → List Int
  -- ── DoublyLinkedListTwo (specialized to Int) ──────────────────
  dll2_setHead          : List Int → Int → List Int
  dll2_setTail          : List Int → Option Int → List Int
  dll2_insert           : List Int → Int → List Int
  dll2_insertAtPosition : List Int → Nat → Int → List Int
  dll2_deleteValue      : List Int → Int → List Int
  dll2_isEmpty          : List Int → Bool
  dll2_headData         : List Int → Option Int
  dll2_tailData         : List Int → Option Int
  -- ── MergeTwoLists ─────────────────────────────────────────────
  merge_fromList   : List Int → List Int
  merge_mergeLists : List Int → List Int → List Int
  -- ── ReverseKGroup ─────────────────────────────────────────────
  revk_append        : List Int → Int → List Int
  revk_reverseKNodes : List Int → Nat → List Int
  -- ── HasLoop (specialized to Int) ──────────────────────────────
  hasLoop_hasLoop : List Int → Bool
  -- ── RotateToTheRight ──────────────────────────────────────────
  rotate_insertNode       : List Int → Int → List Int
  rotate_rotateToTheRight : List Int → Nat → List Int
  -- ── FloydsCycleDetection (specialized to Int) ─────────────────
  floyd_addNode     : List Int → Int → List Int
  floyd_detectCycle : List Int → Bool
  -- ── IsPalindrome ──────────────────────────────────────────────
  palindrome_isPalindrome      : List Int → Bool
  palindrome_isPalindromeStack : List Int → Bool
  palindrome_isPalindromeDict  : List Int → Bool
  -- ── PrintReverse ──────────────────────────────────────────────
  printrev_makeLinkedList : List Int → List Int
  printrev_inReverse      : List Int → List Int
