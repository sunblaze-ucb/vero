-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.PrintReverse

Build a linked list from a list of integers and iterate it in reverse.
`makeLinkedList` wraps a `List Int` as the list (identity in this model);
`inReverse` returns the elements in reverse order.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types (fixed vocabulary) ─────────────────────────────────────
/-- A linked list of integers for reverse printing, modelled as `List Int`. -/
abbrev PrintRev.LinkedList := List Int

namespace PrintRev

-- ── API signatures (fixed vocabulary) ────────────────────────────
abbrev MakeLinkedListSig := List Int → List Int
abbrev InReverseSig      := List Int → List Int

end PrintRev

-- ── Implementations (LLM task) ───────────────────────────────────

-- !benchmark @start code_aux def=printrev_makeLinkedList
-- !benchmark @end code_aux def=printrev_makeLinkedList

def PrintRev.makeLinkedList : PrintRev.MakeLinkedListSig :=
-- !benchmark @start code def=printrev_makeLinkedList
  fun elements => elements
-- !benchmark @end code def=printrev_makeLinkedList

-- !benchmark @start code_aux def=printrev_inReverse
-- !benchmark @end code_aux def=printrev_inReverse

def PrintRev.inReverse : PrintRev.InReverseSig :=
-- !benchmark @start code def=printrev_inReverse
  fun l => l.reverse
-- !benchmark @end code def=printrev_inReverse
