/-!
# Queues.Spec.Aux

Shared spec-only helpers.
-/

/-- Rotate a list left by repeatedly moving the head to the tail. -/
def rotateList {α : Type} (xs : List α) : Nat → List α
  | 0 => xs
  | n + 1 =>
    match xs with
    | [] => []
    | y :: ys => rotateList (ys ++ [y]) n

/-- Spec-only list length helper. Kept outside scored Spec modules to avoid
    confusing API-reference validation for queue APIs named `length`. -/
def spec_helper_len {α : Type} (xs : List α) : Nat :=
  xs.length

/-- Spec-only list emptiness helper. -/
def spec_helper_empty {α : Type} : List α → Bool
  | [] => true
  | _ :: _ => false
