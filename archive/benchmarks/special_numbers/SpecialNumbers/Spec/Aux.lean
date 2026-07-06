/-!
# SpecialNumbers.Spec.Aux

Shared helper predicates for benchmark specifications.
-/

def aux_divides (d n : Int) : Prop :=
  d ≠ 0 ∧ n % d = 0

def aux_sortedStrict : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x < y ∧ aux_sortedStrict (y :: xs)

def aux_allPositive : List Int → Prop
  | [] => True
  | x :: xs => x > 0 ∧ aux_allPositive xs
