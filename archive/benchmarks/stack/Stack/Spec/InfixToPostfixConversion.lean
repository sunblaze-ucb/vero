import Stack.Harness

/-!
# Stack.Spec.InfixToPostfixConversion

Specifications for the shunting-yard infix-to-postfix converter.
Output tokens are space-separated. Unbalanced inputs return `""`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- The empty string converts to the empty string. -/
def spec_infixToPostfix_empty (impl : RepoImpl) : Prop :=
  impl.stack.infixToPostfix "" = ""

/-- Complex expression with alphabetic identifiers from the Python
    doctest, exercising precedence and associativity of `+` and `*`. -/
def spec_infixToPostfix_alphabet_associativity (impl : RepoImpl) : Prop :=
  impl.stack.infixToPostfix "a+b*c+(d*e+f)*g" = "a b c * + d e * f + g * +"

/-- If `balancedParentheses` rejects the expression, `infixToPostfix`
    returns `""`. This is a cross-module guard derived from the
    implementation's top-level guard. -/
def spec_infixToPostfix_unbalanced_implies_empty (impl : RepoImpl) : Prop :=
  ∀ e : String,
    impl.stack.balancedParentheses e = false →
    impl.stack.infixToPostfix e = ""

/-- A single alphanumeric operand is emitted unchanged by the converter. -/
def spec_infixToPostfix_single_operand_general (impl : RepoImpl) : Prop :=
  ∀ c : Char,
    (c.isAlpha || c.isDigit) = true →
    impl.stack.infixToPostfix (String.singleton c) = String.singleton c

/-- A single binary operator between operands is emitted after both operands. -/
def spec_infixToPostfix_single_binary_operator (impl : RepoImpl) : Prop :=
  ∀ lhs rhs op : Char,
    (lhs.isAlpha || lhs.isDigit) = true →
    (rhs.isAlpha || rhs.isDigit) = true →
    op ∈ ['+', '-', '*', '/', '^'] →
    impl.stack.infixToPostfix
      (String.singleton lhs ++ String.singleton op ++ String.singleton rhs) =
      String.singleton lhs ++ " " ++ String.singleton rhs ++ " " ++ String.singleton op
