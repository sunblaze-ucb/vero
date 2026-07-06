import Stack.Impl.BalancedParentheses
import Stack.Impl.Stack

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Stack.Impl.InfixToPostfixConversion

Shunting-yard algorithm converting infix arithmetic expressions to
postfix (Reverse Polish Notation). Output tokens are space-separated.
Returns `""` for unbalanced inputs (Python raises `ValueError`).

Operators: `+` `-` `*` `/` `^` (precedences 1, 1, 2, 2, 3).
`^` is right-associative; all others are left-associative.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── API signatures (no markers — fixed vocabulary) ──────────────────

abbrev InfixToPostfixSig := String → String

-- ── Implementation stubs (LLM task) ────────────────────────────────

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=infixToPostfix
-- Operator precedence (−1 for non-operators, stops popping past '(').
private def itpPrec (c : Char) : Int :=
  match c with
  | '+' | '-' => 1
  | '*' | '/' => 2
  | '^'       => 3
  | _         => -1

-- True when `op` is left-associative.
private def itpLeftAssoc (c : Char) : Bool := c != '^'

-- Pop operators from the stack while they should be output before `op`.
-- Stack head = top. Returns (remaining stack, updated postfix token list).
private def itpPopWhile (op : Char) : List Char → List String → List Char × List String
  | [], pf => ([], pf)
  | (top :: rest), pf =>
    if top == '(' then (top :: rest, pf)
    else if itpPrec top > itpPrec op ||
            (itpPrec top == itpPrec op && itpLeftAssoc op) then
      itpPopWhile op rest (pf ++ [top.toString])
    else (top :: rest, pf)

-- Pop operators until '(' (which is discarded).
private def itpPopUntilOpen : List Char → List String → List Char × List String
  | [], pf => ([], pf)
  | ('(' :: rest), pf => (rest, pf)
  | (top :: rest), pf => itpPopUntilOpen rest (pf ++ [top.toString])

-- Drain remaining operators from the stack at end of input.
private def itpDrain : List Char → List String → List String
  | [], pf => pf
  | (top :: rest), pf => itpDrain rest (pf ++ [top.toString])

-- Main shunting-yard loop.
private def infixToPostfixLoop : List Char → List Char → List String → String
  | [], stack, pf => " ".intercalate (itpDrain stack pf)
  | (c :: rest), stack, pf =>
    if c.isAlpha || c.isDigit then
      infixToPostfixLoop rest stack (pf ++ [c.toString])
    else if c == '(' then
      infixToPostfixLoop rest (c :: stack) pf
    else if c == ')' then
      let (newStack, newPf) := itpPopUntilOpen stack pf
      infixToPostfixLoop rest newStack newPf
    else if c == '+' || c == '-' || c == '*' || c == '/' || c == '^' then
      let (newStack, newPf) := itpPopWhile c stack pf
      infixToPostfixLoop rest (c :: newStack) newPf
    else
      infixToPostfixLoop rest stack pf  -- skip spaces and unknown chars
-- !benchmark @end code_aux def=infixToPostfix

def infixToPostfix : InfixToPostfixSig :=
-- !benchmark @start code def=infixToPostfix
  fun expression =>
    if !balancedParentheses expression then ""
    else infixToPostfixLoop expression.toList [] []
-- !benchmark @end code def=infixToPostfix
