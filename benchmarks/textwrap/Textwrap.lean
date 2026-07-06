import Textwrap.Impl.Wrap
import Textwrap.Bundle
import Textwrap.Harness
import Textwrap.Spec.Wrap
import Textwrap.Test

/-!
# Textwrap

Root import hub for the line-wrapping benchmark.

`wrap chunks width` packs a sequence of words — abstracted to their
lengths (`List Nat`) — into output lines (`List (List Nat)`) so that no
line exceeds `width`, breaking only between whole words. `shorten chunks
width` returns the leading run of words that fits within `width`.
`lineWidth` is a frozen helper: the total occupied width of a line.

A word longer than `width` is not split; it occupies a line of its own.
Whitespace/separator handling and `max_lines`/placeholder behaviour are
out of scope. Behaviour is pinned by `Spec/Wrap.lean`.
-/
