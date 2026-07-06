import Greenery.Harness

/-!
# Greenery.Spec.Fsm

Specifications for the FSM core: `accepts` (run-determinism), `reversed`
(reverse-language + involution), and the headline `reduce` (byte-canonical
minimal DFA — idempotence, language preservation, and the canonical-form
characterization of language equality).

An FSM is modelled over a fixed finite `Nat` alphabet with a complete,
deterministic transition map (an association list `state ↦ (symbol ↦ dest)`).
The frozen predicate `WF` captures greenery's validated `Fsm` invariant: the
alphabet is nonempty; the initial state and all finals are states; and the map
is **total and complete** — every `state × symbol` pair has exactly one entry
whose destination is again a state. The language laws below carry `WF` exactly
where greenery's completeness invariant is required (a machine with a missing
transition is not a well-formed greenery FSM and the crawl-based operations are
undefined on it).

The frozen helper `sameLang` is *bounded language equality*: `A` and `B` agree
on `accepts` for every string over the shared alphabet up to a given length.
The canonical-form specs use it to state, mathlib-free, that two machines
recognise the same language on a tested horizon.

All reference semantics below are stated against frozen **Spec-local** helpers —
`refAssocFind`, `refStep`, `refRunFrom` — defined entirely within this Spec file
(see the "self-contained frozen reference helpers" note), never the
implementation helpers `assocFind` / `step` / `runFrom` from `Impl/Fsm.lean`.

DO NOT MODIFY.
-/

namespace Greenery

/-!
## Self-contained frozen reference helpers

The reference semantics (`langAccepts`, `WF`, `rowComplete`) are rebuilt from
`ref*` helpers defined **entirely within this Spec file**, deliberately NOT
reusing the implementation helpers (`assocFind`, `step`, `runFrom`, …) from
`Impl/Fsm.lean`. Those implementation helpers live inside an agent-editable
`!benchmark` slot (`global_aux`); in `codeproof` mode the sandbox empties that
slot and lets the candidate re-supply them. If the specifications depended on
them, a candidate could redefine `runFrom := fun _ st _ => st` (making
`langAccepts` — hence the language-preservation, canonical-form, De-Morgan and
equivalence obligations — collapse to a degenerate constant that any machine
trivially matches), or `step`/`assocFind` degenerately (breaking `WF` and the
run-determinism law `spec_accepts_fold`), and pass every spec without doing the
real work. Anchoring the specs to these Spec-local, frozen copies makes the
benchmark non-hackable: the reference semantics are fixed no matter what the
candidate supplies for the implementation helpers. Each `ref*` helper is a
byte-for-byte copy of the corresponding frozen `Impl/Fsm.lean` helper.
-/

/-- `refAssocFind d k`: look up key `k` in an association list, returning the
    first matching value or `none`. Frozen Spec-local copy of
    `Impl/Fsm.assocFind`. -/
def refAssocFind {α : Type} (d : List (Nat × α)) (k : Nat) : Option α :=
  match d with
  | [] => none
  | (k', v) :: rest => if k' = k then some v else refAssocFind rest k

/-- `refStep m st sym`: the destination of the transition from state `st` on
    symbol `sym`, or `st` itself when the map has no entry. Frozen Spec-local copy
    of `Impl/Fsm.step`. -/
def refStep (m : Fsm) (st sym : Nat) : Nat :=
  match refAssocFind m.trans st with
  | none => st
  | some row => (refAssocFind row sym).getD st

/-- `refRunFrom m st s`: fold the transition map from state `st` over the string
    `s` — the deterministic left-to-right run underlying the reference language
    semantics. Frozen Spec-local copy of `Impl/Fsm.runFrom`. -/
def refRunFrom (m : Fsm) : Nat → List Nat → Nat
  | st, [] => st
  | st, c :: cs => refRunFrom m (refStep m st c) cs

/-- `rowComplete m row`: every transition row of `m` lists exactly the alphabet
    symbols (as keys) and lands only in states. Frozen structural helper for `WF`,
    stated against the Spec-local `refAssocFind`. -/
def rowComplete (m : Fsm) (row : List (Nat × Nat)) : Bool :=
  m.alphabet.all (fun sym =>
    match refAssocFind row sym with
    | some dest => m.states.contains dest
    | none => false)

/-- `WF m`: `m` is a well-formed greenery FSM — nonempty alphabet; `initial` and
    every `final` are states; and the transition map is total and complete
    (every state has a row, and every row is defined on exactly the alphabet with
    destinations in `states`). Frozen predicate mirroring greenery's `__init__`
    validation. -/
def WF (m : Fsm) : Prop :=
  m.alphabet ≠ [] ∧
  m.states.contains m.initial = true ∧
  (∀ f, m.finals.contains f = true → m.states.contains f = true) ∧
  (∀ st, m.states.contains st = true →
    ∃ row, refAssocFind m.trans st = some row ∧ rowComplete m row = true)

/-- `langAccepts m s`: the reference language semantics of `m` — run the frozen
    deterministic fold `refRunFrom` from the initial state and test finality. This
    is a frozen *semantic model* (built only from the frozen Spec-local helpers
    `refRunFrom` / `refStep`), deliberately independent of the scored `accepts`
    API (and of any candidate-supplied `runFrom` / `step`) so that canonical-form
    obligations can be stated against genuine semantics rather than against the
    implementation under test. Frozen helper. -/
def langAccepts (m : Fsm) (s : List Nat) : Bool :=
  m.finals.contains (refRunFrom m m.initial s)

/-- `sameLang n a b`: bounded language equality — `a` and `b` accept exactly the
    same strings over `a`'s alphabet up to length `n`, measured by the frozen
    reference semantics `langAccepts`. Frozen semantic helper used to state
    canonical-form obligations mathlib-free. -/
def sameLang (n : Nat) (a b : Fsm) : Prop :=
  ∀ s : List Nat, s.length ≤ n → (∀ c ∈ s, a.alphabet.contains c = true) →
    langAccepts a s = langAccepts b s

/-- `symbolsIn alpha s`: every symbol of `s` is in `alpha`. Frozen predicate
    restricting witnesses/strings to the alphabet. -/
def symbolsIn (alpha : List Nat) (s : List Nat) : Prop :=
  ∀ c, c ∈ s → alpha.contains c = true

/-- `stateReachable m st`: some alphabet-string drives the frozen run
    `refRunFrom` from the initial state to `st`. Frozen semantic helper. -/
def stateReachable (m : Fsm) (st : Nat) : Prop :=
  ∃ s : List Nat, symbolsIn m.alphabet s ∧ refRunFrom m m.initial s = st

/-- `stateDistinguishable m p q`: some alphabet-string separates states `p` and
    `q` — running the frozen fold from `p` versus `q` lands on states of
    differing finality. Frozen semantic helper (residual-language inequality). -/
def stateDistinguishable (m : Fsm) (p q : Nat) : Prop :=
  ∃ s : List Nat, symbolsIn m.alphabet s ∧
    m.finals.contains (refRunFrom m p s) ≠ m.finals.contains (refRunFrom m q s)

/-- `liveFrom m st`: some alphabet-string drives the frozen fold from `st` into a
    final state. Frozen semantic helper (nonempty residual language). -/
def liveFrom (m : Fsm) (st : Nat) : Prop :=
  ∃ s : List Nat, symbolsIn m.alphabet s ∧
    m.finals.contains (refRunFrom m st s) = true

/-- `sinkRow alpha st`: a transition row sending every alphabet symbol to `st`.
    Frozen helper. -/
def sinkRow (alpha : List Nat) (st : Nat) : List (Nat × Nat) :=
  alpha.map (fun sym => (sym, st))

/-- `addUnreachableSink m fresh`: `m` with one extra non-final state `fresh` whose
    row self-loops on every symbol. Frozen structural perturbation. -/
def addUnreachableSink (m : Fsm) (fresh : Nat) : Fsm :=
  { alphabet := m.alphabet
    states := m.states ++ [fresh]
    initial := m.initial
    finals := m.finals
    trans := m.trans ++ [(fresh, sinkRow m.alphabet fresh)] }

end Greenery

open Greenery

-- ════════════════════════════════════════════════════════════════
-- accepts: run-determinism (the frozen fold)
-- ════════════════════════════════════════════════════════════════

/-- Run-determinism: `accepts` is exactly "run the deterministic fold `refRunFrom`
    from the initial state, then test finality". For every machine and string,
    `accepts m s = m.finals.contains (refRunFrom m m.initial s)`, where
    `refRunFrom` is the frozen Spec-local left-to-right transition fold. This pins
    `accepts` to the genuine deterministic run over the transition map (a
    right-to-left reader, a set-of-reachable-states reader, or an all-paths NFA
    reader all fail). Stated against the frozen `refRunFrom` (not the editable
    implementation helper), so the law cannot be gamed by co-degenerating a
    candidate-supplied `runFrom`. Over `impl.greenery.accepts`, `refRunFrom`,
    `refStep`. -/
def spec_accepts_fold (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm) (s : List Nat),
    impl.greenery.accepts m s = m.finals.contains (refRunFrom m m.initial s)

/-- Empty-string acceptance: `accepts m []` is exactly "the initial state is
    final". Pins the base case of the run. Over `impl.greenery.accepts`. -/
def spec_accepts_nil (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm), impl.greenery.accepts m [] = m.finals.contains m.initial

-- ════════════════════════════════════════════════════════════════
-- reduce: byte-canonical minimal DFA (the headline)
-- ════════════════════════════════════════════════════════════════

/-- `reduce` idempotence: `reduce` lands on a fixed point — reducing an
    already-reduced machine changes nothing, `reduce (reduce m) = reduce m`.
    Pins `reduce` as a genuine canonicalizer (a `reduce := id` fails
    `spec_reduce_canonical`; a non-idempotent minimizer fails this). Over
    `impl.greenery.reduce`. -/
def spec_reduce_idempotent (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm), impl.greenery.reduce (impl.greenery.reduce m) = impl.greenery.reduce m

/-- `reduce` preserves the language: for a well-formed `m`, `reduce m` accepts
    exactly the same strings as `m` on every tested horizon `n` — minimization
    never changes the recognised language. Over `impl.greenery.reduce`,
    `sameLang`, `WF`. -/
def spec_reduce_preserves_lang (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm) (n : Nat), WF m → sameLang n m (impl.greenery.reduce m)

/-- Canonical form decides equality: if two well-formed machines recognise the
    same language (agree on `accepts` for **all** strings — the `n`-bounded
    statement for every `n`), then their reductions are **byte-identical** —
    `reduce A = reduce B`. This is the crown property: `reduce` is a *canonical
    form* for regular languages, so equivalent machines minimize to literally the
    same FSM. It defeats every reward hack that returns a merely language-correct
    but non-canonical machine (different labeling, extra dead states, …). Over
    `impl.greenery.reduce`, `sameLang`, `WF`. -/
def spec_reduce_canonical (impl : RepoImpl) : Prop :=
  ∀ (a b : Fsm), WF a → WF b → a.alphabet = b.alphabet →
    (∀ n, sameLang n a b) → impl.greenery.reduce a = impl.greenery.reduce b

-- ════════════════════════════════════════════════════════════════
-- reversed: reverse language + involution
-- ════════════════════════════════════════════════════════════════

/-- `reversed` reverses the language: for a well-formed `m` and any string `s`
    over the alphabet, `reversed m` accepts `s` iff `m` accepts the reverse of
    `s` — `accepts (reversed m) s = accepts m s.reverse`. Pins `reversed` to the
    genuine reverse-language automaton (the subset construction on the reverse
    NFA), not a same-language copy. Over `impl.greenery.reversed`,
    `impl.greenery.accepts`, `WF`. -/
def spec_reversed_lang (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm) (s : List Nat), WF m → (∀ c ∈ s, m.alphabet.contains c = true) →
    impl.greenery.accepts (impl.greenery.reversed m) s = impl.greenery.accepts m s.reverse

/-- `reversed` involution on the language: reversing twice recovers the original
    language — for well-formed `m`, `reversed (reversed m)` accepts exactly what
    `m` does on every horizon. (This is Brzozowski's route to `reduce`.) Over
    `impl.greenery.reversed`, `sameLang`, `WF`. -/
def spec_reversed_involution (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm) (n : Nat), WF m → sameLang n m (impl.greenery.reversed (impl.greenery.reversed m))

-- ════════════════════════════════════════════════════════════════
-- reduce: minimality + reachable/distinguishable partition (Myhill–Nerode)
-- ════════════════════════════════════════════════════════════════

/-- State-count minimality: `reduce m` has no more states than *any* well-formed
    machine recognising the same language. For well-formed `m`, `b` over a shared
    alphabet with `sameLang n m b` for every `n`, `(reduce m).states.length ≤
    b.states.length`. This pins `reduce` to the minimal DFA state count — no
    equivalent machine is smaller. Over `impl.greenery.reduce`, `sameLang`,
    `WF`. -/
def spec_reduce_state_count_minimal (impl : RepoImpl) : Prop :=
  ∀ (m b : Fsm), WF m → WF b → m.alphabet = b.alphabet →
    (∀ n, sameLang n m b) →
    (impl.greenery.reduce m).states.length ≤ b.states.length

/-- Every reduced state is reachable: for well-formed `m`, `reduce m` is itself
    well-formed and every one of its states is reached from the initial state by
    some alphabet-string (via the frozen fold `refRunFrom`). Pins `reduce`
    against emitting unreachable states. Over `impl.greenery.reduce`,
    `stateReachable`, `WF`. -/
def spec_reduce_all_states_reachable (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm), WF m →
    let r := impl.greenery.reduce m
    WF r ∧ ∀ st, r.states.contains st = true → stateReachable r st

/-- Reduced states are pairwise distinguishable: for well-formed `m`, `reduce m`
    is well-formed and any two distinct states have a separating alphabet-string
    (they disagree on finality after the frozen fold). Pins `reduce` against
    emitting language-equivalent (mergeable) states — the minimal-DFA
    distinguishability partition. Over `impl.greenery.reduce`,
    `stateDistinguishable`, `WF`. -/
def spec_reduce_pairwise_distinguishable (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm), WF m →
    let r := impl.greenery.reduce m
    WF r ∧ ∀ p q, r.states.contains p = true → r.states.contains q = true →
      p ≠ q → stateDistinguishable r p q

/-- Reduced dead states collapse to a single self-looping sink: for well-formed
    `m`, `reduce m` is well-formed, has at most one non-live state (no
    alphabet-string reaches a final state from it), and that state self-loops on
    every symbol (via the frozen `refStep`). Pins the dead-state collapse of
    minimization. Over `impl.greenery.reduce`, `liveFrom`, `refStep`, `WF`. -/
def spec_reduce_dead_states_are_unique_sink (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm), WF m →
    let r := impl.greenery.reduce m
    WF r ∧
      (∀ p q, r.states.contains p = true → r.states.contains q = true →
        ¬ liveFrom r p → ¬ liveFrom r q → p = q) ∧
      (∀ p sym, r.states.contains p = true → r.alphabet.contains sym = true →
        ¬ liveFrom r p → refStep r p sym = p)

/-- Adding an unreachable dead sink is invisible to `reduce`: for a well-formed
    `m` and a `fresh` label that is neither a state nor a transition key,
    `reduce (addUnreachableSink m fresh) = reduce m` — byte-identically. Pins
    `reduce` against retaining unreachable structural noise. Over
    `impl.greenery.reduce`, `addUnreachableSink`, `refAssocFind`, `WF`. -/
def spec_reduce_ignores_added_unreachable_sink (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm) (fresh : Nat), WF m →
    m.states.contains fresh = false →
    refAssocFind m.trans fresh = none →
    impl.greenery.reduce (addUnreachableSink m fresh) = impl.greenery.reduce m
