import Greenery.Impl.Fsm
import Greenery.Impl.Algebra
import Greenery.Bundle
import Greenery.Harness
import Greenery.Spec.Fsm
import Greenery.Spec.Algebra
import Greenery.Test

/-!
# Greenery

Root import hub: regular languages as finite state machines, ported from the
`greenery` library (`greenery/fsm.py`, qntm, MIT). An `Fsm` is modelled
mathlib-free over a fixed finite `Nat` alphabet with a complete, deterministic
transition map (an association list `state ↦ (symbol ↦ dest)`).

FSM core (`Impl/Fsm`, `Spec/Fsm`): `accepts` (the deterministic run), `reversed`
(reverse-language automaton via the subset construction), and the headline
`reduce` (Brzozowski minimization `reversed ∘ reversed`, producing the
**byte-canonical** minimal DFA — states relabeled `0 … n-1` by a deterministic
BFS over the sorted alphabet).

Boolean algebra (`Impl/Algebra`, `Spec/Algebra`): `fsmUnion` (`|`), `fsmInter`
(`&`), `everythingbut` (complement `~`), and `equivalent` (language equality,
decided by canonical form). The crown properties are `reduce` idempotence and
language-preservation, the canonical-form characterization of equivalence
(`equivalent A B ↔ reduce A = reduce B`, and equivalent machines minimize to the
*same* FSM), De Morgan (`~(A ∪ B) ≡ ~A ∩ ~B`), and the double-complement /
reversal involutions.

Behaviour is pinned by `Spec/Fsm.lean` and `Spec/Algebra.lean`.
-/
