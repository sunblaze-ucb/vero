/-!
# LinkedList.Spec.Aux

Shared helper predicates used only by specification modules.
-/

/-- Boolean ascending-order check used by merge specs. -/
def spec_helper_isSortedAsc : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => x ≤ y && spec_helper_isSortedAsc (y :: rest)

/-- Boolean duplicate check: true iff some value appears more than once. -/
def spec_helper_hasDuplicate : List Int → Bool
  | [] => false
  | x :: xs => xs.contains x || spec_helper_hasDuplicate xs
