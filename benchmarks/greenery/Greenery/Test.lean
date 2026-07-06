import Greenery.Impl.Fsm
import Greenery.Impl.Algebra

/-!
# Greenery.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations in `Impl/Fsm.lean` and `Impl/Algebra.lean`, checked
against the `greenery` library (greenery 4.2.2, `greenery/fsm.py`).

FSMs are modelled over a fixed finite `Nat` alphabet (symbol `i` = the i-th
alphabet symbol in ascending order); the transition map is a complete
association list `state ↦ (symbol ↦ dest)`. This matches greenery's validated
`Fsm` invariant (a total, deterministic map) faithfully. The reduced-FSM
structures below were captured from a byte-canonical reference model that
matches greenery's `reduce`/`union`/`intersection`/`everythingbut`/`reversed`
outputs (identical minimal-DFA size and structure up to the alphabet-symbol
labeling convention).

Test FSMs over alphabet `{0, 1}`:
- `fA` = "accepts exactly the one-symbol string `[0]`" (state 0 start, 1 final, 2 dead).
- `fB` = "accepts exactly `[1]`".
- `fStar` = "accepts any run of `0`s" (`0*`).
Test FSMs over alphabet `{0, 1, 2}`:
- `fX` = "accepts `[0,1]` or `[0,2]`" (i.e. `a(b|c)`), minimal (4 states).
- `fY` = a non-minimal FSM recognising the same language (5 states, redundant accept).

DO NOT MODIFY — infrastructure.
-/

open Greenery

def tA : Fsm := {
  alphabet := [0, 1], states := [0, 1, 2], initial := 0, finals := [1],
  trans := [(0, [(0, 1), (1, 2)]), (1, [(0, 2), (1, 2)]), (2, [(0, 2), (1, 2)])] }
def tB : Fsm := {
  alphabet := [0, 1], states := [0, 1, 2], initial := 0, finals := [1],
  trans := [(0, [(0, 2), (1, 1)]), (1, [(0, 2), (1, 2)]), (2, [(0, 2), (1, 2)])] }
def tStar : Fsm := {
  alphabet := [0, 1], states := [0, 1], initial := 0, finals := [0],
  trans := [(0, [(0, 0), (1, 1)]), (1, [(0, 1), (1, 1)])] }
def tX : Fsm := {
  alphabet := [0, 1, 2], states := [0, 1, 2, 3], initial := 0, finals := [3],
  trans := [(0, [(0, 1), (1, 2), (2, 2)]), (1, [(0, 2), (1, 3), (2, 3)]),
            (2, [(0, 2), (1, 2), (2, 2)]), (3, [(0, 2), (1, 2), (2, 2)])] }
def tY : Fsm := {
  alphabet := [0, 1, 2], states := [0, 1, 2, 3, 4], initial := 0, finals := [3, 4],
  trans := [(0, [(0, 1), (1, 2), (2, 2)]), (1, [(0, 2), (1, 3), (2, 4)]),
            (2, [(0, 2), (1, 2), (2, 2)]), (3, [(0, 2), (1, 2), (2, 2)]),
            (4, [(0, 2), (1, 2), (2, 2)])] }

-- Expected canonical structures (captured from the greenery-matching reference model).
def eA : Fsm := {
  alphabet := [0, 1], states := [0, 1, 2], initial := 0, finals := [1],
  trans := [(0, [(0, 1), (1, 2)]), (1, [(0, 2), (1, 2)]), (2, [(0, 2), (1, 2)])] }
def eStar : Fsm := {
  alphabet := [0, 1], states := [0, 1], initial := 0, finals := [0],
  trans := [(0, [(0, 0), (1, 1)]), (1, [(0, 1), (1, 1)])] }
def eUnion : Fsm := {
  alphabet := [0, 1], states := [0, 1, 2], initial := 0, finals := [1],
  trans := [(0, [(0, 1), (1, 1)]), (1, [(0, 2), (1, 2)]), (2, [(0, 2), (1, 2)])] }
def eInterEmpty : Fsm := {
  alphabet := [0, 1], states := [0], initial := 0, finals := [],
  trans := [(0, [(0, 0), (1, 0)])] }
def eCompl : Fsm := {
  alphabet := [0, 1], states := [0, 1, 2], initial := 0, finals := [0, 2],
  trans := [(0, [(0, 1), (1, 2)]), (1, [(0, 2), (1, 2)]), (2, [(0, 2), (1, 2)])] }

-- ── accepts ──────────────────────────────────────────────────────
#guard accepts tA [0] == true
#guard accepts tA [1] == false
#guard accepts tA [] == false
#guard accepts tA [0, 0] == false
#guard accepts tStar [0, 0, 0] == true
#guard accepts tStar [0, 1] == false
#guard accepts tX [0, 1] == true
#guard accepts tX [0, 2] == true
#guard accepts tX [0, 0] == false

-- ── reduce (byte-canonical minimal DFA) ──────────────────────────
-- fA is already minimal: reduce is structure-preserving here.
#guard decide (reduce tA = eA)
-- fStar reduces to a 2-state minimal DFA.
#guard decide (reduce tStar = eStar)
-- CROWN: the non-minimal fY reduces to the SAME 4-state minimal DFA as fX.
#guard decide (reduce tX = reduce tY)
#guard (reduce tX).states.length == 4
#guard (reduce tY).states.length == 4

-- ── reversed ─────────────────────────────────────────────────────
-- fA is symmetric under reversal (one-symbol language), so reversed fA ≅ fA structurally.
#guard decide (reversed tA = eA)
-- reversed reverses the language:
#guard accepts (reversed tX) [1, 0] == accepts tX [0, 1]   -- true
#guard accepts (reversed tX) [2, 0] == accepts tX [0, 2]   -- true

-- ── fsmUnion ─────────────────────────────────────────────────────
#guard decide (fsmUnion tA tB = eUnion)
#guard accepts (fsmUnion tA tB) [0] == true
#guard accepts (fsmUnion tA tB) [1] == true
#guard accepts (fsmUnion tA tB) [0, 1] == false

-- ── fsmInter ─────────────────────────────────────────────────────
-- fA ∩ fB is empty (disjoint languages) → single dead state, no finals.
#guard decide (fsmInter tA tB = eInterEmpty)
#guard accepts (fsmInter tA tB) [0] == false
#guard accepts (fsmInter tX tX) [0, 1] == true

-- ── everythingbut (complement) ───────────────────────────────────
#guard decide (everythingbut tA = eCompl)
#guard accepts (everythingbut tA) [0] == false
#guard accepts (everythingbut tA) [1] == true
#guard accepts (everythingbut tA) [] == true

-- ── equivalent ───────────────────────────────────────────────────
#guard equivalent tX tY == true       -- same language, canonical forms agree
#guard equivalent tA tB == false      -- disjoint languages
#guard equivalent tA tA == true       -- reflexive
#guard equivalent (everythingbut (everythingbut tA)) tA == true   -- double complement
-- crown: equivalent (via symmetric-difference-empty) agrees with reduce-equality
#guard equivalent tX tY == decide (reduce tX = reduce tY)
#guard equivalent tA tB == decide (reduce tA = reduce tB)

-- ── cross-API algebraic laws ─────────────────────────────────────
-- union commutativity (byte-canonical): reduce (A ∪ B) = reduce (B ∪ A)
#guard decide (reduce (fsmUnion tA tB) = reduce (fsmUnion tB tA))
-- union idempotence (byte-canonical): reduce (A ∪ A) = reduce A
#guard decide (reduce (fsmUnion tA tA) = reduce tA)
-- dual De Morgan (language): ~(A ∩ B) ≡ ~A ∪ ~B on a witness string
#guard accepts (everythingbut (fsmInter tA tB)) [0] ==
       accepts (fsmUnion (everythingbut tA) (everythingbut tB)) [0]
#guard accepts (everythingbut (fsmInter tA tB)) [1] ==
       accepts (fsmUnion (everythingbut tA) (everythingbut tB)) [1]
