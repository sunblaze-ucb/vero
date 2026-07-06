import TinyUnsat.Harness

/-!
# TinyUnsat.Spec.Core — DO NOT MODIFY.

Three specs engineered to exercise three grader paths:

- ``spec_impossible``       — no impl can satisfy (``unsat_<S>`` provable).
- ``spec_answer_is_one``    — satisfied iff impl.tiny.answer = 1.
- ``spec_answer_is_two``    — satisfied iff impl.tiny.answer = 2.

Pair (answer_is_one, answer_is_two) is jointly unsatisfiable
(Nat can't be both 1 and 2) but each is individually satisfiable.
-/

/-- Trivially impossible. -/
def spec_impossible (impl : RepoImpl) : Prop :=
  impl.tiny.answer = impl.tiny.answer + 1

/-- ``answer = 1``. -/
def spec_answer_is_one (impl : RepoImpl) : Prop :=
  impl.tiny.answer = 1

/-- ``answer = 2``. -/
def spec_answer_is_two (impl : RepoImpl) : Prop :=
  impl.tiny.answer = 2
