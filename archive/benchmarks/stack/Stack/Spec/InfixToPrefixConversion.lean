import Stack.Harness

/-!
# Stack.Spec.InfixToPrefixConversion

Specifications for `infix2Postfix` (a simpler no-space shunting-yard)
and `infix2Prefix` (reverse input → swap brackets → postfix → reverse
result).

DO NOT MODIFY — frozen curator-given content.
-/

/-- The empty expression is a shared identity case for both converters. -/
def spec_infix2_empty_agreement (impl : RepoImpl) : Prop :=
  impl.stack.infix2Postfix "" = "" ∧
  impl.stack.infix2Prefix "" = ""

/-- Concrete input/output pairs from the Python doctests. -/
def spec_infix2Postfix_examples (impl : RepoImpl) : Prop :=
  impl.stack.infix2Postfix "a+b" = "ab+" ∧
  impl.stack.infix2Postfix "a+b^c" = "abc^+" ∧
  impl.stack.infix2Postfix "1*((-a)*2+b)" = "1a-2*b+*"

/-- Concrete input/output pairs from the Python doctests. -/
def spec_infix2Prefix_examples (impl : RepoImpl) : Prop :=
  impl.stack.infix2Prefix "a+b" = "+ab" ∧
  impl.stack.infix2Prefix "a+b^c" = "+a^bc" ∧
  impl.stack.infix2Prefix "1*((-a)*2+b)" = "*1+*-a2b"

/-- A single operand is unchanged by both conversion variants. -/
def spec_infix2_single_operand (impl : RepoImpl) : Prop :=
  impl.stack.infix2Postfix "a" = "a" ∧
  impl.stack.infix2Prefix "a" = "a"

/-- Spec-side mirror of the bracket swap used to define prefix conversion. -/
def spec_helper_swapBrackets (cs : List Char) : List Char :=
  cs.map fun c =>
    if c == '(' then ')'
    else if c == ')' then '('
    else c

/-- Reverse the input and swap parentheses, matching the prefix converter. -/
def spec_helper_reverseSwap (expr : String) : String :=
  String.ofList (spec_helper_swapBrackets expr.toList.reverse)

/-- A single alphanumeric operand is unchanged by both conversion variants. -/
def spec_infix2_single_operand_general (impl : RepoImpl) : Prop :=
  ∀ c : Char,
    (c.isAlpha || c.isDigit) = true →
    impl.stack.infix2Postfix (String.singleton c) = String.singleton c ∧
    impl.stack.infix2Prefix (String.singleton c) = String.singleton c

/-- A single binary operator between operands is emitted after both operands in postfix. -/
def spec_infix2Postfix_single_binary_operator (impl : RepoImpl) : Prop :=
  ∀ lhs rhs op : Char,
    (lhs.isAlpha || lhs.isDigit) = true →
    (rhs.isAlpha || rhs.isDigit) = true →
    op ∈ ['+', '-', '*', '/', '%', '^'] →
    impl.stack.infix2Postfix
      (String.singleton lhs ++ String.singleton op ++ String.singleton rhs) =
      String.singleton lhs ++ String.singleton rhs ++ String.singleton op

/-- A single binary operator between operands is emitted before both operands in prefix. -/
def spec_infix2Prefix_single_binary_operator (impl : RepoImpl) : Prop :=
  ∀ lhs rhs op : Char,
    (lhs.isAlpha || lhs.isDigit) = true →
    (rhs.isAlpha || rhs.isDigit) = true →
    op ∈ ['+', '-', '*', '/', '%', '^'] →
    impl.stack.infix2Prefix
      (String.singleton lhs ++ String.singleton op ++ String.singleton rhs) =
      String.singleton op ++ String.singleton lhs ++ String.singleton rhs

/-- Prefix conversion is reverse-swapped postfix conversion, by construction. -/
def spec_infix2Prefix_reverse_postfix_law (impl : RepoImpl) : Prop :=
  ∀ expr : String,
    impl.stack.infix2Prefix expr =
      String.ofList (impl.stack.infix2Postfix (spec_helper_reverseSwap expr)).toList.reverse
