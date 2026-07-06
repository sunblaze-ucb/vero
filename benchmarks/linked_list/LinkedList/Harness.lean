import LinkedList.Bundle

/-!
# LinkedList.Harness

Benchmark harness: `RepoImpl` structure (one field for the LinkedList
package), `canonical` instance wiring all reference implementations,
and the `joint_unsat` macro for `codeproof`-mode joint unsatisfiability
proofs.

DO NOT MODIFY this file. This is the benchmark infrastructure.
-/

-- ── Implementation bundle (one field per package) ─────────────────

structure RepoImpl where
  linkedList : LinkedListBundle

-- ── Canonical instance ────────────────────────────────────────────

def canonical : RepoImpl where
  linkedList := {
    -- SinglyLinkedList
    sll_insertHead  := SLL.insertHead
    sll_insertTail  := SLL.insertTail
    sll_insertNth   := SLL.insertNth
    sll_deleteHead  := SLL.deleteHead
    sll_deleteTail  := SLL.deleteTail
    sll_deleteNth   := SLL.deleteNth
    sll_isEmpty     := SLL.isEmpty
    sll_reverse     := SLL.reverse
    -- FromSequence
    fromSeq_makeLinkedList := FromSeq.makeLinkedList
    -- DoublyLinkedList
    dll_insertAtHead := DLL.insertAtHead
    dll_insertAtTail := DLL.insertAtTail
    dll_insertAtNth  := DLL.insertAtNth
    dll_deleteHead   := DLL.deleteHead
    dll_deleteTail   := DLL.deleteTail
    dll_deleteAtNth  := DLL.deleteAtNth
    dll_deleteData   := DLL.deleteData
    dll_isEmpty      := DLL.isEmpty
    -- CircularLinkedList
    cll_insertHead  := CLL.insertHead
    cll_insertTail  := CLL.insertTail
    cll_insertNth   := CLL.insertNth
    cll_deleteFront := CLL.deleteFront
    cll_deleteTail  := CLL.deleteTail
    cll_deleteNth   := CLL.deleteNth
    cll_isEmpty     := CLL.isEmpty
    -- DequeDoubly
    deque_first       := Deque.first
    deque_last        := Deque.last
    deque_addFirst    := Deque.addFirst
    deque_addLast     := Deque.addLast
    deque_removeFirst := Deque.removeFirst
    deque_removeLast  := Deque.removeLast
    deque_isEmpty     := Deque.isEmpty
    -- MiddleElementOfLinkedList
    midll_push          := MidLL.push
    midll_middleElement := MidLL.middleElement
    -- LinkedListInit
    lli_add     := LLI.add
    lli_remove  := LLI.remove
    lli_isEmpty := LLI.isEmpty
    lli_length  := LLI.length
    -- SkipList
    skipl_insert := SkipL.insert
    skipl_delete := SkipL.delete
    skipl_find   := SkipL.find
    -- SwapNodes
    swap_push      := Swap.push
    swap_swapNodes := Swap.swapNodes
    -- DoublyLinkedListTwo
    dll2_setHead          := DLL2.setHead
    dll2_setTail          := DLL2.setTail
    dll2_insert           := DLL2.insert
    dll2_insertAtPosition := DLL2.insertAtPosition
    dll2_deleteValue      := DLL2.deleteValue
    dll2_isEmpty          := DLL2.isEmpty
    dll2_headData         := DLL2.headData
    dll2_tailData         := DLL2.tailData
    -- MergeTwoLists
    merge_fromList   := Merge.fromList
    merge_mergeLists := Merge.mergeLists
    -- ReverseKGroup
    revk_append        := RevK.append
    revk_reverseKNodes := RevK.reverseKNodes
    -- HasLoop
    hasLoop_hasLoop := HasLoop.hasLoop
    -- RotateToTheRight
    rotate_insertNode       := Rotate.insertNode
    rotate_rotateToTheRight := Rotate.rotateToTheRight
    -- FloydsCycleDetection
    floyd_addNode     := Floyd.addNode
    floyd_detectCycle := Floyd.detectCycle
    -- IsPalindrome
    palindrome_isPalindrome      := Palindrome.isPalindrome
    palindrome_isPalindromeStack := Palindrome.isPalindromeStack
    palindrome_isPalindromeDict  := Palindrome.isPalindromeDict
    -- PrintReverse
    printrev_makeLinkedList := PrintRev.makeLinkedList
    printrev_inReverse      := PrintRev.inReverse
  }

-- ── joint_unsat macro ─────────────────────────────────────────────

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
