import Stack.Impl.Stack
import Stack.Impl.BalancedParentheses
import Stack.Impl.InfixToPostfixConversion
import Stack.Impl.InfixToPrefixConversion
import Stack.Impl.DijkstrasTwoStackAlgorithm
import Stack.Bundle
import Stack.Harness

/-!
# Stack.Test

`#guard` conformance tests. Every guard dispatches through `canonical.stack.*`
so the harness wiring is exercised end-to-end. Coverage target: ≥3 guards per
API (empty / typical / edge — multi-element / nested / mismatched when sensible).

Pre-agent-gen replaces marker content in `Impl/*.lean` with `sorry`; these
guards catch regressions in the reference impls.

DO NOT MODIFY — infrastructure.
-/

-- ── Stack.isEmpty ────────────────────────────────────────────────────
#guard canonical.stack.isEmpty (Stack.empty : Stack Nat) == true
#guard canonical.stack.isEmpty (Stack.push 5 Stack.empty) == false
#guard canonical.stack.isEmpty (Stack.fromList [1, 2, 3] : Stack Nat) == false
#guard canonical.stack.isEmpty ([] : Stack Nat) == true

-- ── Stack.size ───────────────────────────────────────────────────────
#guard canonical.stack.size (Stack.empty : Stack Nat) == 0
#guard canonical.stack.size (Stack.push 5 Stack.empty) == 1
#guard canonical.stack.size (Stack.push 1 (Stack.push 2 Stack.empty)) == 2
#guard canonical.stack.size (canonical.stack.fromList [1, 2, 3, 4]) == 4

-- ── Stack.isFull ─────────────────────────────────────────────────────
#guard canonical.stack.isFull (Stack.empty : Stack Nat) 10 == false
#guard canonical.stack.isFull (Stack.push 5 Stack.empty) 1 == true
#guard canonical.stack.isFull (Stack.push 1 (Stack.push 2 Stack.empty)) 2 == true

-- ── Stack.peek ───────────────────────────────────────────────────────
#guard canonical.stack.peek (Stack.empty : Stack Nat) == none
#guard canonical.stack.peek (Stack.push 5 Stack.empty) == some 5
#guard canonical.stack.peek (canonical.stack.fromList [1, 2, 3]) == some 3

-- ── Stack.pop ────────────────────────────────────────────────────────
#guard canonical.stack.pop (Stack.empty : Stack Nat) == none
#guard canonical.stack.pop (Stack.push 5 Stack.empty) == some (5, Stack.empty)
#guard canonical.stack.pop (canonical.stack.fromList [1, 2, 3]) == some (3, canonical.stack.fromList [1, 2])

-- ── Stack.contains ───────────────────────────────────────────────────
#guard canonical.stack.contains 5 (Stack.empty : Stack Nat) == false
#guard canonical.stack.contains 5 (Stack.push 5 Stack.empty) == true
#guard canonical.stack.contains 3 (Stack.push 5 Stack.empty) == false

-- ── Stack.fromList ───────────────────────────────────────────────────
#guard canonical.stack.fromList ([] : List Nat) == (Stack.empty : Stack Nat)
#guard canonical.stack.fromList [1] == Stack.push 1 Stack.empty
#guard canonical.stack.fromList [1, 2, 3] == Stack.push 1 (Stack.push 2 (Stack.push 3 Stack.empty))

-- ── balancedParentheses ──────────────────────────────────────────────
#guard canonical.stack.balancedParentheses "([]{})" == true
#guard canonical.stack.balancedParentheses "[()]{}{[()()]()}" == true
#guard canonical.stack.balancedParentheses "[(])" == false
#guard canonical.stack.balancedParentheses "1+2*3-4" == true
#guard canonical.stack.balancedParentheses "" == true

-- ── infixToPostfix ───────────────────────────────────────────────────
#guard canonical.stack.infixToPostfix "" == ""
#guard canonical.stack.infixToPostfix "3+2" == "3 2 +"
#guard canonical.stack.infixToPostfix "(3+4)*5-6" == "3 4 + 5 * 6 -"
#guard canonical.stack.infixToPostfix "(1+2)*3/4-5" == "1 2 + 3 * 4 / 5 -"
#guard canonical.stack.infixToPostfix "a+b*c+(d*e+f)*g" == "a b c * + d e * f + g * +"

-- ── infix2Postfix ────────────────────────────────────────────────────
#guard canonical.stack.infix2Postfix "a+b^c" == "abc^+"
#guard canonical.stack.infix2Postfix "1*((-a)*2+b)" == "1a-2*b+*"
#guard canonical.stack.infix2Postfix "" == ""
#guard canonical.stack.infix2Postfix "a+b" == "ab+"

-- ── infix2Prefix ─────────────────────────────────────────────────────
#guard canonical.stack.infix2Prefix "a+b^c" == "+a^bc"
#guard canonical.stack.infix2Prefix "1*((-a)*2+b)" == "*1+*-a2b"
#guard canonical.stack.infix2Prefix "" == ""
#guard canonical.stack.infix2Prefix "a+b" == "+ab"

-- ── dijkstrasTwoStackAlgorithm ───────────────────────────────────────
#guard canonical.stack.dijkstrasTwoStackAlgorithm "(5 + 3)" == 8
#guard canonical.stack.dijkstrasTwoStackAlgorithm "((9 - (2 + 9)) + (8 - 1))" == 5
#guard canonical.stack.dijkstrasTwoStackAlgorithm "((((3 - 2) - (2 + 3)) + (2 - 4)) + 3)" == -3
#guard canonical.stack.dijkstrasTwoStackAlgorithm "(2 + 3)" == 5
#guard canonical.stack.dijkstrasTwoStackAlgorithm "(7 - 3)" == 4
