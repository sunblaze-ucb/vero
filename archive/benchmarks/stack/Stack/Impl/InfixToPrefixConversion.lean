import Stack.Impl.InfixToPostfixConversion

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Stack.Impl.InfixToPrefixConversion

Two-function module for infix-to-postfix and infix-to-prefix conversion.
`infix2Postfix` uses a simpler algorithm (no associativity distinction,
no space separators) distinct from `infixToPostfix`.
`infix2Prefix` reverses the input, swaps brackets, calls `infix2Postfix`,
then reverses the result.

Python source: `infix_to_prefix_conversion.py`.
Print statements in the original are dropped — @review human: omission noted.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── API signatures (no markers — fixed vocabulary) ──────────────────

abbrev Infix2PostfixSig := String → String
abbrev Infix2PrefixSig  := String → String

-- ── Implementation stubs (LLM task) ────────────────────────────────

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=infix2Postfix
-- Operator priority table (^ = 3, */ = 2, +- = 1).
private def i2pPriority (c : Char) : Nat :=
  match c with
  | '^'             => 3
  | '*' | '/' | '%' => 2
  | '+' | '-'       => 1
  | _               => 0

-- Pop while current operator has priority ≤ top (and top ≠ '(').
private def i2pPopWhile (op : Char) : List Char → List Char → List Char × List Char
  | [], pf => ([], pf)
  | (top :: rest), pf =>
    if top == '(' then (top :: rest, pf)
    else if i2pPriority op ≤ i2pPriority top then
      i2pPopWhile op rest (pf ++ [top])
    else (top :: rest, pf)

-- Pop operators until '(' (discarded), used on ')'.
private def i2pPopUntilOpen : List Char → List Char → List Char × List Char
  | [], pf => ([], pf)
  | ('(' :: rest), pf => (rest, pf)
  | (top :: rest), pf => i2pPopUntilOpen rest (pf ++ [top])

-- Drain remaining stack; skip any unmatched '(' (error in Python, ignored here).
private def i2pDrain : List Char → List Char → List Char
  | [], pf => pf
  | ('(' :: _), pf => pf   -- invalid expression guard
  | (top :: rest), pf => i2pDrain rest (pf ++ [top])

-- Main loop: stack-head = top (LIFO via prepend).
private def infix2PostfixLoop : List Char → List Char → List Char → String
  | [], stack, pf => String.ofList (i2pDrain stack pf)
  | (c :: rest), stack, pf =>
    if c.isAlpha || c.isDigit then
      infix2PostfixLoop rest stack (pf ++ [c])
    else if c == '(' then
      infix2PostfixLoop rest (c :: stack) pf
    else if c == ')' then
      let (newStack, newPf) := i2pPopUntilOpen stack pf
      infix2PostfixLoop rest newStack newPf
    else if c == '+' || c == '-' || c == '*' || c == '/' || c == '^' || c == '%' then
      let (newStack, newPf) := i2pPopWhile c stack pf
      infix2PostfixLoop rest (c :: newStack) newPf
    else
      infix2PostfixLoop rest stack pf  -- skip spaces / unknown chars
-- !benchmark @end code_aux def=infix2Postfix

def infix2Postfix : Infix2PostfixSig :=
-- !benchmark @start code def=infix2Postfix
  fun expr => infix2PostfixLoop expr.toList [] []
-- !benchmark @end code def=infix2Postfix

-- !benchmark @start code_aux def=infix2Prefix
-- Swap '(' ↔ ')' in a char list.
private def swapBrackets (cs : List Char) : List Char :=
  cs.map fun c =>
    if c == '(' then ')'
    else if c == ')' then '('
    else c
-- !benchmark @end code_aux def=infix2Prefix

def infix2Prefix : Infix2PrefixSig :=
-- !benchmark @start code def=infix2Prefix
  fun expr =>
    let reversed := expr.toList.reverse
    let swapped  := swapBrackets reversed
    let pfix     := infix2Postfix (String.ofList swapped)
    String.ofList pfix.toList.reverse
-- !benchmark @end code def=infix2Prefix
