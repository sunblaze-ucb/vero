import LinkedList.Harness

/-!
# LinkedList.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations through the canonical bundle.
Before the LLM sees the benchmark, the pipeline replaces marker contents
with `sorry` — these guards catch regressions in the reference impls.

Every guard goes through `canonical.linkedList.<api>` so that the suite
exercises the same wiring the joint_unsat / codeproof grader uses.

DO NOT MODIFY — infrastructure.
-/

-- ── SinglyLinkedList ─────────────────────────────────────────────
-- sll_insertHead
#guard canonical.linkedList.sll_insertHead [] 1 == [1]
#guard canonical.linkedList.sll_insertHead [2, 3] 1 == [1, 2, 3]
#guard canonical.linkedList.sll_insertHead [5] 9 == [9, 5]
-- sll_insertTail
#guard canonical.linkedList.sll_insertTail [] 1 == [1]
#guard canonical.linkedList.sll_insertTail [1, 2] 3 == [1, 2, 3]
#guard canonical.linkedList.sll_insertTail [7] 8 == [7, 8]
-- sll_insertNth
#guard canonical.linkedList.sll_insertNth [] 0 1 == [1]
#guard canonical.linkedList.sll_insertNth [1, 3] 1 2 == [1, 2, 3]
#guard canonical.linkedList.sll_insertNth [1, 2] 0 9 == [9, 1, 2]
#guard canonical.linkedList.sll_insertNth [1, 2] 2 9 == [1, 2, 9]
-- sll_deleteHead
#guard canonical.linkedList.sll_deleteHead [] == none
#guard canonical.linkedList.sll_deleteHead [1, 2, 3] == some (1, [2, 3])
#guard canonical.linkedList.sll_deleteHead [42] == some (42, [])
-- sll_deleteTail
#guard canonical.linkedList.sll_deleteTail [] == none
#guard canonical.linkedList.sll_deleteTail [1, 2, 3] == some (3, [1, 2])
#guard canonical.linkedList.sll_deleteTail [42] == some (42, [])
-- sll_deleteNth
#guard canonical.linkedList.sll_deleteNth [] 0 == none
#guard canonical.linkedList.sll_deleteNth [1, 2, 3] 1 == some (2, [1, 3])
#guard canonical.linkedList.sll_deleteNth [1, 2, 3] 0 == some (1, [2, 3])
#guard canonical.linkedList.sll_deleteNth [1, 2, 3] 5 == none
-- sll_isEmpty
#guard canonical.linkedList.sll_isEmpty [] == true
#guard canonical.linkedList.sll_isEmpty [1] == false
#guard canonical.linkedList.sll_isEmpty [1, 2, 3] == false
-- sll_reverse
#guard canonical.linkedList.sll_reverse [] == ([] : List Int)
#guard canonical.linkedList.sll_reverse [1] == [1]
#guard canonical.linkedList.sll_reverse [1, 2, 3] == [3, 2, 1]

-- ── FromSequence ──────────────────────────────────────────────────
-- fromSeq_makeLinkedList
#guard canonical.linkedList.fromSeq_makeLinkedList [] == none
#guard canonical.linkedList.fromSeq_makeLinkedList [1, 2, 3] == some [1, 2, 3]
#guard canonical.linkedList.fromSeq_makeLinkedList [42] == some [42]

-- ── DoublyLinkedList ──────────────────────────────────────────────
-- dll_insertAtHead
#guard canonical.linkedList.dll_insertAtHead [] 1 == [1]
#guard canonical.linkedList.dll_insertAtHead [2, 3] 1 == [1, 2, 3]
#guard canonical.linkedList.dll_insertAtHead [5] 9 == [9, 5]
-- dll_insertAtTail
#guard canonical.linkedList.dll_insertAtTail [] 1 == [1]
#guard canonical.linkedList.dll_insertAtTail [1, 2] 3 == [1, 2, 3]
#guard canonical.linkedList.dll_insertAtTail [7] 8 == [7, 8]
-- dll_insertAtNth
#guard canonical.linkedList.dll_insertAtNth [] 0 1 == [1]
#guard canonical.linkedList.dll_insertAtNth [1, 3] 1 2 == [1, 2, 3]
#guard canonical.linkedList.dll_insertAtNth [1, 2] 0 9 == [9, 1, 2]
-- dll_deleteHead
#guard canonical.linkedList.dll_deleteHead [] == none
#guard canonical.linkedList.dll_deleteHead [1, 2, 3] == some (1, [2, 3])
#guard canonical.linkedList.dll_deleteHead [9] == some (9, [])
-- dll_deleteTail
#guard canonical.linkedList.dll_deleteTail [] == none
#guard canonical.linkedList.dll_deleteTail [1, 2, 3] == some (3, [1, 2])
#guard canonical.linkedList.dll_deleteTail [9] == some (9, [])
-- dll_deleteAtNth
#guard canonical.linkedList.dll_deleteAtNth [] 0 == none
#guard canonical.linkedList.dll_deleteAtNth [1, 2, 3] 1 == some (2, [1, 3])
#guard canonical.linkedList.dll_deleteAtNth [1, 2, 3] 0 == some (1, [2, 3])
#guard canonical.linkedList.dll_deleteAtNth [1, 2, 3] 5 == none
-- dll_deleteData
#guard canonical.linkedList.dll_deleteData [] 1 == none
#guard canonical.linkedList.dll_deleteData [1, 2, 3] 2 == some (2, [1, 3])
#guard canonical.linkedList.dll_deleteData [1, 2, 3] 9 == none
-- dll_isEmpty
#guard canonical.linkedList.dll_isEmpty [] == true
#guard canonical.linkedList.dll_isEmpty [1] == false
#guard canonical.linkedList.dll_isEmpty [1, 2, 3] == false

-- ── CircularLinkedList ────────────────────────────────────────────
-- cll_insertHead
#guard canonical.linkedList.cll_insertHead [] 1 == [1]
#guard canonical.linkedList.cll_insertHead [2, 3] 1 == [1, 2, 3]
#guard canonical.linkedList.cll_insertHead [5] 9 == [9, 5]
-- cll_insertTail
#guard canonical.linkedList.cll_insertTail [] 1 == [1]
#guard canonical.linkedList.cll_insertTail [1, 2] 3 == [1, 2, 3]
#guard canonical.linkedList.cll_insertTail [7] 8 == [7, 8]
-- cll_insertNth
#guard canonical.linkedList.cll_insertNth [] 0 1 == [1]
#guard canonical.linkedList.cll_insertNth [1, 3] 1 2 == [1, 2, 3]
#guard canonical.linkedList.cll_insertNth [1, 2] 0 9 == [9, 1, 2]
-- cll_deleteFront
#guard canonical.linkedList.cll_deleteFront [] == none
#guard canonical.linkedList.cll_deleteFront [1, 2, 3] == some (1, [2, 3])
#guard canonical.linkedList.cll_deleteFront [42] == some (42, [])
-- cll_deleteTail
#guard canonical.linkedList.cll_deleteTail [] == none
#guard canonical.linkedList.cll_deleteTail [1, 2, 3] == some (3, [1, 2])
#guard canonical.linkedList.cll_deleteTail [42] == some (42, [])
-- cll_deleteNth
#guard canonical.linkedList.cll_deleteNth [] 0 == none
#guard canonical.linkedList.cll_deleteNth [1, 2, 3] 1 == some (2, [1, 3])
#guard canonical.linkedList.cll_deleteNth [1, 2, 3] 0 == some (1, [2, 3])
-- cll_isEmpty
#guard canonical.linkedList.cll_isEmpty [] == true
#guard canonical.linkedList.cll_isEmpty [1] == false
#guard canonical.linkedList.cll_isEmpty [1, 2, 3] == false

-- ── DequeDoubly ───────────────────────────────────────────────────
-- deque_first
#guard canonical.linkedList.deque_first [] == none
#guard canonical.linkedList.deque_first [1, 2, 3] == some 1
#guard canonical.linkedList.deque_first [42] == some 42
-- deque_last
#guard canonical.linkedList.deque_last [] == none
#guard canonical.linkedList.deque_last [1, 2, 3] == some 3
#guard canonical.linkedList.deque_last [42] == some 42
-- deque_addFirst
#guard canonical.linkedList.deque_addFirst [] 1 == [1]
#guard canonical.linkedList.deque_addFirst [2, 3] 1 == [1, 2, 3]
#guard canonical.linkedList.deque_addFirst [5] 9 == [9, 5]
-- deque_addLast
#guard canonical.linkedList.deque_addLast [] 1 == [1]
#guard canonical.linkedList.deque_addLast [1, 2] 3 == [1, 2, 3]
#guard canonical.linkedList.deque_addLast [7] 8 == [7, 8]
-- deque_removeFirst
#guard canonical.linkedList.deque_removeFirst [] == none
#guard canonical.linkedList.deque_removeFirst [1, 2, 3] == some (1, [2, 3])
#guard canonical.linkedList.deque_removeFirst [42] == some (42, [])
-- deque_removeLast
#guard canonical.linkedList.deque_removeLast [] == none
#guard canonical.linkedList.deque_removeLast [1, 2, 3] == some (3, [1, 2])
#guard canonical.linkedList.deque_removeLast [42] == some (42, [])
-- deque_isEmpty
#guard canonical.linkedList.deque_isEmpty [] == true
#guard canonical.linkedList.deque_isEmpty [1] == false
#guard canonical.linkedList.deque_isEmpty [1, 2, 3] == false

-- ── MiddleElementOfLinkedList ─────────────────────────────────────
-- midll_push
#guard canonical.linkedList.midll_push [] 1 == [1]
#guard canonical.linkedList.midll_push [2, 3] 1 == [1, 2, 3]
#guard canonical.linkedList.midll_push [5] 9 == [9, 5]
-- midll_middleElement
#guard canonical.linkedList.midll_middleElement [] == none
#guard canonical.linkedList.midll_middleElement [1, 2, 3] == some 2
#guard canonical.linkedList.midll_middleElement [1, 2, 3, 4, 5] == some 3

-- ── LinkedListInit ────────────────────────────────────────────────
-- lli_add
#guard canonical.linkedList.lli_add [] 1 0 == [1]
#guard canonical.linkedList.lli_add [1, 3] 2 1 == [1, 2, 3]
#guard canonical.linkedList.lli_add [1, 2] 9 0 == [9, 1, 2]
-- lli_remove
#guard canonical.linkedList.lli_remove [] == none
#guard canonical.linkedList.lli_remove [1, 2, 3] == some (1, [2, 3])
#guard canonical.linkedList.lli_remove [42] == some (42, [])
-- lli_isEmpty
#guard canonical.linkedList.lli_isEmpty [] == true
#guard canonical.linkedList.lli_isEmpty [1] == false
#guard canonical.linkedList.lli_isEmpty [1, 2, 3] == false
-- lli_length
#guard canonical.linkedList.lli_length [] == 0
#guard canonical.linkedList.lli_length [1] == 1
#guard canonical.linkedList.lli_length [1, 2, 3] == 3

-- ── SkipList (Int keys, Int values) ───────────────────────────────
-- skipl_insert
#guard canonical.linkedList.skipl_insert [] 1 10 == [(1, 10)]
#guard canonical.linkedList.skipl_insert [(1, 10), (3, 30)] 2 20 == [(1, 10), (2, 20), (3, 30)]
#guard canonical.linkedList.skipl_insert [(1, 10)] 1 99 == [(1, 99)]
-- skipl_delete
#guard canonical.linkedList.skipl_delete [] 1 == []
#guard canonical.linkedList.skipl_delete [(1, 10), (2, 20), (3, 30)] 2 == [(1, 10), (3, 30)]
#guard canonical.linkedList.skipl_delete [(1, 10)] 9 == [(1, 10)]
-- skipl_find
#guard canonical.linkedList.skipl_find [] 1 == none
#guard canonical.linkedList.skipl_find [(1, 10), (2, 20)] 2 == some 20
#guard canonical.linkedList.skipl_find [(1, 10), (2, 20)] 9 == none

-- ── SwapNodes ─────────────────────────────────────────────────────
-- swap_push
#guard canonical.linkedList.swap_push [] 1 == [1]
#guard canonical.linkedList.swap_push [2, 3] 1 == [1, 2, 3]
#guard canonical.linkedList.swap_push [5] 9 == [9, 5]
-- swap_swapNodes
#guard canonical.linkedList.swap_swapNodes [1, 2, 3] 1 3 == [3, 2, 1]
#guard canonical.linkedList.swap_swapNodes [1, 2, 3] 1 1 == [1, 2, 3]
#guard canonical.linkedList.swap_swapNodes [1, 2, 3, 4] 2 4 == [1, 4, 3, 2]

-- ── DoublyLinkedListTwo ───────────────────────────────────────────
-- dll2_setHead
#guard canonical.linkedList.dll2_setHead [] 9 == [9]
#guard canonical.linkedList.dll2_setHead [1, 2, 3] 9 == [9, 2, 3]
#guard canonical.linkedList.dll2_setHead [7] 9 == [9]
-- dll2_setTail
#guard canonical.linkedList.dll2_setTail [1, 2, 3] (some 9) == [1, 2, 9]
#guard canonical.linkedList.dll2_setTail [1, 2, 3] none == [1, 2]
#guard canonical.linkedList.dll2_setTail [] (some 9) == [9]
-- dll2_insert
#guard canonical.linkedList.dll2_insert [] 1 == [1]
#guard canonical.linkedList.dll2_insert [2, 3] 1 == [1, 2, 3]
#guard canonical.linkedList.dll2_insert [5] 9 == [9, 5]
-- dll2_insertAtPosition
#guard canonical.linkedList.dll2_insertAtPosition [] 0 1 == [1]
#guard canonical.linkedList.dll2_insertAtPosition [1, 3] 1 2 == [1, 2, 3]
#guard canonical.linkedList.dll2_insertAtPosition [1, 2] 2 9 == [1, 2, 9]
-- dll2_deleteValue
#guard canonical.linkedList.dll2_deleteValue [] 1 == []
#guard canonical.linkedList.dll2_deleteValue [1, 2, 3, 2] 2 == [1, 3]
#guard canonical.linkedList.dll2_deleteValue [1, 2, 3] 9 == [1, 2, 3]
-- dll2_isEmpty
#guard canonical.linkedList.dll2_isEmpty [] == true
#guard canonical.linkedList.dll2_isEmpty [1] == false
#guard canonical.linkedList.dll2_isEmpty [1, 2, 3] == false
-- dll2_headData
#guard canonical.linkedList.dll2_headData [] == none
#guard canonical.linkedList.dll2_headData [1, 2, 3] == some 1
#guard canonical.linkedList.dll2_headData [42] == some 42
-- dll2_tailData
#guard canonical.linkedList.dll2_tailData [] == none
#guard canonical.linkedList.dll2_tailData [1, 2, 3] == some 3
#guard canonical.linkedList.dll2_tailData [42] == some 42

-- ── MergeTwoLists ─────────────────────────────────────────────────
-- merge_fromList
#guard canonical.linkedList.merge_fromList [] == ([] : List Int)
#guard canonical.linkedList.merge_fromList [3, 1, 2] == [1, 2, 3]
#guard canonical.linkedList.merge_fromList [5] == [5]
-- merge_mergeLists
#guard canonical.linkedList.merge_mergeLists [] [1, 2] == [1, 2]
#guard canonical.linkedList.merge_mergeLists [1, 3] [2, 4] == [1, 2, 3, 4]
#guard canonical.linkedList.merge_mergeLists [1, 2] [] == [1, 2]

-- ── ReverseKGroup ─────────────────────────────────────────────────
-- revk_append
#guard canonical.linkedList.revk_append [] 1 == [1]
#guard canonical.linkedList.revk_append [1, 2] 3 == [1, 2, 3]
#guard canonical.linkedList.revk_append [7] 8 == [7, 8]
-- revk_reverseKNodes
#guard canonical.linkedList.revk_reverseKNodes [1, 2, 3, 4, 5] 2 == [2, 1, 4, 3, 5]
#guard canonical.linkedList.revk_reverseKNodes [1, 2, 3] 3 == [3, 2, 1]
#guard canonical.linkedList.revk_reverseKNodes [1, 2, 3, 4, 5] 1 == [1, 2, 3, 4, 5]

-- ── HasLoop ───────────────────────────────────────────────────────
-- hasLoop_hasLoop (duplicate value = loop proxy)
#guard canonical.linkedList.hasLoop_hasLoop [] == false
#guard canonical.linkedList.hasLoop_hasLoop [1, 2, 3] == false
#guard canonical.linkedList.hasLoop_hasLoop [1, 2, 1] == true

-- ── RotateToTheRight ──────────────────────────────────────────────
-- rotate_insertNode
#guard canonical.linkedList.rotate_insertNode [] 1 == [1]
#guard canonical.linkedList.rotate_insertNode [1, 2] 3 == [1, 2, 3]
#guard canonical.linkedList.rotate_insertNode [7] 8 == [7, 8]
-- rotate_rotateToTheRight
#guard canonical.linkedList.rotate_rotateToTheRight [1, 2, 3, 4, 5] 2 == [4, 5, 1, 2, 3]
#guard canonical.linkedList.rotate_rotateToTheRight [1, 2, 3] 0 == [1, 2, 3]
#guard canonical.linkedList.rotate_rotateToTheRight [] 5 == ([] : List Int)

-- ── FloydsCycleDetection ──────────────────────────────────────────
-- floyd_addNode
#guard canonical.linkedList.floyd_addNode [] 1 == [1]
#guard canonical.linkedList.floyd_addNode [1, 2] 3 == [1, 2, 3]
#guard canonical.linkedList.floyd_addNode [7] 8 == [7, 8]
-- floyd_detectCycle (duplicate value = cycle proxy)
#guard canonical.linkedList.floyd_detectCycle [] == false
#guard canonical.linkedList.floyd_detectCycle [1, 2, 3] == false
#guard canonical.linkedList.floyd_detectCycle [1, 2, 1] == true

-- ── IsPalindrome ──────────────────────────────────────────────────
-- palindrome_isPalindrome
#guard canonical.linkedList.palindrome_isPalindrome [] == true
#guard canonical.linkedList.palindrome_isPalindrome [1, 2, 1] == true
#guard canonical.linkedList.palindrome_isPalindrome [1, 2, 3] == false
-- palindrome_isPalindromeStack
#guard canonical.linkedList.palindrome_isPalindromeStack [] == true
#guard canonical.linkedList.palindrome_isPalindromeStack [1, 2, 1] == true
#guard canonical.linkedList.palindrome_isPalindromeStack [1, 2, 3] == false
-- palindrome_isPalindromeDict
#guard canonical.linkedList.palindrome_isPalindromeDict [] == true
#guard canonical.linkedList.palindrome_isPalindromeDict [1, 2, 1] == true
#guard canonical.linkedList.palindrome_isPalindromeDict [1, 2, 3] == false

-- ── PrintReverse ──────────────────────────────────────────────────
-- printrev_makeLinkedList
#guard canonical.linkedList.printrev_makeLinkedList [] == ([] : List Int)
#guard canonical.linkedList.printrev_makeLinkedList [69, 88, 73] == [69, 88, 73]
#guard canonical.linkedList.printrev_makeLinkedList [7] == [7]
-- printrev_inReverse
#guard canonical.linkedList.printrev_inReverse [] == ([] : List Int)
#guard canonical.linkedList.printrev_inReverse [69, 88, 73] == [73, 88, 69]
#guard canonical.linkedList.printrev_inReverse [1] == [1]
