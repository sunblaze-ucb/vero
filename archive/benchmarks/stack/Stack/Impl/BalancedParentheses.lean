import Stack.Impl.Stack

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Stack.Impl.BalancedParentheses

Stack-based checker for balanced bracket strings. Supports `(`, `)`,
`[`, `]`, `{`, `}`. Non-bracket characters are ignored.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── API signatures (no markers — fixed vocabulary) ──────────────────

abbrev BalancedParenthesesSig := String → Bool

-- ── Implementation stubs (LLM task) ────────────────────────────────

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=balancedParentheses
-- Helpers: bracket matching check using a local LIFO list (head = top).
private def matchingClose (c : Char) : Char :=
  match c with
  | '(' => ')'
  | '[' => ']'
  | '{' => '}'
  | _   => c

private def isOpen (c : Char) : Bool :=
  c == '(' || c == '[' || c == '{'

private def isClose (c : Char) : Bool :=
  c == ')' || c == ']' || c == '}'

private def balancedParenthesesAux : List Char → List Char → Bool
  | [], stack => stack.isEmpty
  | (c :: rest), stack =>
    if isOpen c then balancedParenthesesAux rest (c :: stack)
    else if isClose c then
      match stack with
      | [] => false
      | top :: restStack =>
        if matchingClose top == c then balancedParenthesesAux rest restStack
        else false
    else balancedParenthesesAux rest stack  -- non-bracket chars ignored
-- !benchmark @end code_aux def=balancedParentheses

def balancedParentheses : BalancedParenthesesSig :=
-- !benchmark @start code def=balancedParentheses
  fun parentheses => balancedParenthesesAux parentheses.toList []
-- !benchmark @end code def=balancedParentheses
