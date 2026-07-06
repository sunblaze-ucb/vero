import Stack.Impl.Stack

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Stack.Impl.DijkstrasTwoStackAlgorithm

Dijkstra's two-stack algorithm for evaluating fully-parenthesised
arithmetic expressions containing single-digit operands and the
operators `+`, `-`, `*`, `/`.

The return type is `Int`. Division uses Lean's truncated integer
division; this matches Python for the non-negative test cases provided.
`@review human: integer division used instead of Python's truediv;
 acceptable because no test case exercises division on non-integers.`

Python source: `dijkstras_two_stack_algorithm.py` (print statements dropped).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── API signatures (no markers — fixed vocabulary) ──────────────────

abbrev DijkstrasTwoStackAlgorithmSig := String → Int

-- ── Implementation stubs (LLM task) ────────────────────────────────

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=dijkstrasTwoStackAlgorithm
-- Apply an arithmetic operator to two Int operands.
private def applyOp (op : Char) (a b : Int) : Int :=
  match op with
  | '+' => a + b
  | '-' => a - b
  | '*' => a * b
  | '/' => a / b
  | _   => 0

-- Two-stack evaluation loop.
-- `operands` and `operators` are LIFO lists (head = top).
private def dijkstraLoop : List Char → List Int → List Char → Int
  | [], operands, _ => operands.head?.getD 0
  | (c :: rest), operands, operators =>
    if c.isDigit then
      dijkstraLoop rest ((c.toNat - '0'.toNat : Int) :: operands) operators
    else if c == '+' || c == '-' || c == '*' || c == '/' then
      dijkstraLoop rest operands (c :: operators)
    else if c == ')' then
      match operators, operands with
      | (op :: restOps), (num1 :: num2 :: restNums) =>
        let total := applyOp op num2 num1
        dijkstraLoop rest (total :: restNums) restOps
      | _, _ => dijkstraLoop rest operands operators  -- malformed input guard
    else
      dijkstraLoop rest operands operators  -- skip '(' and spaces
-- !benchmark @end code_aux def=dijkstrasTwoStackAlgorithm

def dijkstrasTwoStackAlgorithm : DijkstrasTwoStackAlgorithmSig :=
-- !benchmark @start code def=dijkstrasTwoStackAlgorithm
  fun equation => dijkstraLoop equation.toList [] []
-- !benchmark @end code def=dijkstrasTwoStackAlgorithm
