import Stack.Harness

/-!
# Stack.Spec.DijkstrasTwoStackAlgorithm

Specifications for Dijkstra's two-stack algorithm, which evaluates
fully-parenthesised arithmetic expressions over single-digit operands
with operators `+`, `-`, `*`, `/`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- Concrete input/output pairs from the Python doctests. -/
def spec_dijkstra_examples (impl : RepoImpl) : Prop :=
  impl.stack.dijkstrasTwoStackAlgorithm "(5 + 3)" = 8 ∧
  impl.stack.dijkstrasTwoStackAlgorithm "((9 - (2 + 9)) + (8 - 1))" = 5 ∧
  impl.stack.dijkstrasTwoStackAlgorithm "((((3 - 2) - (2 + 3)) + (2 - 4)) + 3)" = -3

/-- Each of the four supported operators works correctly on a simple
    two-operand parenthesised expression. -/
def spec_dijkstra_simple_binary (impl : RepoImpl) : Prop :=
  impl.stack.dijkstrasTwoStackAlgorithm "(2 + 3)" = 5 ∧
  impl.stack.dijkstrasTwoStackAlgorithm "(7 - 3)" = 4 ∧
  impl.stack.dijkstrasTwoStackAlgorithm "(4 * 2)" = 8 ∧
  impl.stack.dijkstrasTwoStackAlgorithm "(8 / 2)" = 4

/-- General single-digit binary expressions for all supported operators. -/
def spec_dijkstra_single_digit_binary_ops (impl : RepoImpl) : Prop :=
  (∀ a b : Nat, a < 10 → b < 10 →
    impl.stack.dijkstrasTwoStackAlgorithm
      ("(" ++ toString a ++ " + " ++ toString b ++ ")") =
        (a : Int) + (b : Int)) ∧
  (∀ a b : Nat, a < 10 → b < 10 →
    impl.stack.dijkstrasTwoStackAlgorithm
      ("(" ++ toString a ++ " - " ++ toString b ++ ")") =
        (a : Int) - (b : Int)) ∧
  (∀ a b : Nat, a < 10 → b < 10 →
    impl.stack.dijkstrasTwoStackAlgorithm
      ("(" ++ toString a ++ " * " ++ toString b ++ ")") =
        (a : Int) * (b : Int)) ∧
  (∀ a b : Nat, a < 10 → b < 10 → b ≠ 0 → a % b = 0 →
    impl.stack.dijkstrasTwoStackAlgorithm
      ("(" ++ toString a ++ " / " ++ toString b ++ ")") =
        (a : Int) / (b : Int))
