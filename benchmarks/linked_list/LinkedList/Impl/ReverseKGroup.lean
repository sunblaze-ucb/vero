-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.ReverseKGroup

Reverse nodes in groups of k. `append` adds an integer to the end;
`reverseKNodes` reverses groups of k consecutive nodes, leaving
the remainder (length mod k nodes) in original order.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types (fixed vocabulary) ─────────────────────────────────────
/-- A linked list for k-group reversal, modelled as `List Int`. -/
abbrev RevK.LinkedList := List Int

namespace RevK

-- ── API signatures (fixed vocabulary) ────────────────────────────
abbrev AppendSig        := List Int → Int → List Int
abbrev ReverseKNodesSig := List Int → Nat → List Int

-- ── Implementations (LLM task) ───────────────────────────────────

-- !benchmark @start code_aux def=revk_append
-- !benchmark @end code_aux def=revk_append

def append : AppendSig :=
-- !benchmark @start code def=revk_append
  fun l a => l ++ [a]
-- !benchmark @end code def=revk_append

-- !benchmark @start code_aux def=revk_reverseKNodes
-- Helper: reverse in groups of k using fuel for termination.
-- Fuel = lst.length ensures the function always terminates.
-- @review human: termination via fuel (= lst.length at call site).
private def reverseKHelper (k : Nat) : Nat → List Int → List Int → List Int
  | 0,        lst, acc => acc ++ lst
  | _,        [],  acc => acc
  | fuel + 1, lst, acc =>
    if k == 0 then acc ++ lst
    else
      let group := lst.take k
      let rest  := lst.drop k
      if group.length < k then
        acc ++ group
      else
        reverseKHelper k fuel rest (acc ++ group.reverse)
-- !benchmark @end code_aux def=revk_reverseKNodes

def reverseKNodes : ReverseKNodesSig :=
-- !benchmark @start code def=revk_reverseKNodes
  fun l k => reverseKHelper k l.length l []
-- !benchmark @end code def=revk_reverseKNodes

end RevK
