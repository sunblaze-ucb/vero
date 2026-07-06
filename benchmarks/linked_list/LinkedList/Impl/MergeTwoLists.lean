-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.MergeTwoLists

Merge two sorted linked lists. The Python `SortedLinkedList` stores
integers in ascending order. `fromList` builds a sorted list from any
integer sequence; `mergeLists` merges two sorted lists into one.
Modelled as `List Int` in sorted ascending order.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types (fixed vocabulary) ─────────────────────────────────────
/-- A sorted linked list of integers, modelled as `List Int`. -/
abbrev Merge.SortedLinkedList := List Int

namespace Merge

-- ── API signatures (fixed vocabulary) ────────────────────────────
abbrev FromListSig   := List Int → List Int
abbrev MergeListsSig := List Int → List Int → List Int

-- ── Implementations (LLM task) ───────────────────────────────────

-- !benchmark @start code_aux def=merge_fromList
-- Insertion sort: insert x into already-sorted list in ascending order.
private def insertSorted (x : Int) : List Int → List Int
  | []      => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

-- Sort a list of integers in ascending order using insertion sort.
private def insertionSort : List Int → List Int
  | []      => []
  | x :: xs => insertSorted x (insertionSort xs)
-- !benchmark @end code_aux def=merge_fromList

def fromList : FromListSig :=
-- !benchmark @start code def=merge_fromList
  fun ints => insertionSort ints
-- !benchmark @end code def=merge_fromList

-- !benchmark @start code_aux def=merge_mergeLists
-- Merge two sorted lists in ascending order.
-- @review human: termination via sum of lengths (both inputs decrease)
private def mergeSorted : List Int → List Int → List Int
  | [],       ys       => ys
  | xs,       []       => xs
  | x :: xs', y :: ys' =>
    if x ≤ y then x :: mergeSorted xs' (y :: ys')
    else y :: mergeSorted (x :: xs') ys'
termination_by xs ys => xs.length + ys.length
-- !benchmark @end code_aux def=merge_mergeLists

def mergeLists : MergeListsSig :=
-- !benchmark @start code def=merge_mergeLists
  fun a b => mergeSorted a b
-- !benchmark @end code def=merge_mergeLists

end Merge
