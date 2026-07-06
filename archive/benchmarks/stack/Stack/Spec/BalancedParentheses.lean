import Stack.Harness

/-!
# Stack.Spec.BalancedParentheses

Specifications for the balanced-parentheses checker. Non-bracket
characters are silently ignored; the three supported bracket flavours
are `()`, `[]`, and `{}`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- The empty string is balanced. -/
def spec_balanced_empty (impl : RepoImpl) : Prop :=
  impl.stack.balancedParentheses "" = true

/-- The three basic matched pairs each return `true`; a reversed pair returns `false`. -/
def spec_balanced_simple_pairs (impl : RepoImpl) : Prop :=
  ∀ left right : Char,
    (left, right) ∈ [('(', ')'), ('[', ']'), ('{', '}')] →
    impl.stack.balancedParentheses (String.singleton left ++ String.singleton right) = true ∧
    impl.stack.balancedParentheses (String.singleton right ++ String.singleton left) = false

/-- Strings with unclosed opening brackets are unbalanced. -/
def spec_balanced_unmatched_open (impl : RepoImpl) : Prop :=
  ∀ left : Char,
    left ∈ ['(', '[', '{'] →
    impl.stack.balancedParentheses (String.singleton left) = false ∧
    impl.stack.balancedParentheses (String.singleton left ++ String.singleton left) = false

/-- Balanced strings are closed under concatenation. -/
def spec_balanced_concat_closed (impl : RepoImpl) : Prop :=
  ∀ a b : String,
    impl.stack.balancedParentheses a = true →
    impl.stack.balancedParentheses b = true →
    impl.stack.balancedParentheses (a ++ b) = true

/-- Non-bracket wrapper characters are ignored by the checker. -/
def spec_balanced_ignores_nonbrackets (impl : RepoImpl) : Prop :=
  ∀ s : String,
    impl.stack.balancedParentheses ("a" ++ s ++ "1") =
    impl.stack.balancedParentheses s
