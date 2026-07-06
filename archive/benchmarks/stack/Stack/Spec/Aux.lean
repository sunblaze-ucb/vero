/-!
# Stack.Spec.Aux

Shared helpers for stack specifications.

DO NOT MODIFY — frozen curator-given content.
-/

/-- The last element of a list, if any. -/
def listLast? {α : Type} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: xs => listLast? xs
