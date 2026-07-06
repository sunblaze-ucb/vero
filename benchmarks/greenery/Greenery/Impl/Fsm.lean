-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Greenery.Impl.Fsm

Finite-state-machine core, ported from the `greenery` library
(`greenery/fsm.py`, qntm, MIT). An `Fsm` represents a regular language as a
deterministic finite automaton with a **complete** transition map.

Representation (mathlib-free, all core `Nat`/`List`):
- `alphabet : List Nat` — the finite symbol set (symbol codes), deduplicated
  and ascending.
- `states : List Nat` — the state labels.
- `initial : Nat` — the start state.
- `finals : List Nat` — the accepting states (a subset of `states`).
- `trans : List (Nat × List (Nat × Nat))` — the transition map as an
  association list `state ↦ (symbol ↦ dest)`. In a well-formed FSM the map is
  **total and complete**: every `state × symbol` pair has exactly one entry
  whose destination is again a state (greenery's validated `__init__`
  invariant).

APIs in this module: `accepts` (run the machine over a string), `reversed`
(reverse-language automaton via the subset construction), and `reduce`
(Brzozowski minimization `reversed ∘ reversed` — the **byte-canonical**
minimal DFA). The universal engine is `crawl`, a fuel-bounded breadth-first
exploration that discovers reachable meta-states in order and relabels them
`0 … n-1` over the *sorted* alphabet — this deterministic relabeling is what
makes `reduce` byte-canonical.

All functions are total, terminating `def`s (recursion is fuel-bounded or
structural); no `Float`.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Greenery

/-- A finite state machine over a finite `Nat` alphabet. Mirrors greenery's
    `Fsm` dataclass. The transition map `trans` is an association list
    `state ↦ (symbol ↦ dest)`; in a well-formed FSM it is total and complete. -/
structure Fsm where
  alphabet : List Nat
  states   : List Nat
  initial  : Nat
  finals   : List Nat
  trans    : List (Nat × List (Nat × Nat))
deriving Repr, DecidableEq, Inhabited

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `accepts m s`: does FSM `m` accept the string `s` (a list of symbols)? -/
abbrev AcceptsSig := Fsm → List Nat → Bool

/-- `reversed m`: the FSM recognising the reversed language of `m`. -/
abbrev ReversedSig := Fsm → Fsm

/-- `reduce m`: the byte-canonical minimal DFA equivalent to `m`
    (`reversed ∘ reversed`). -/
abbrev ReduceSig := Fsm → Fsm

end Greenery

-- !benchmark @start global_aux
namespace Greenery

/-- `assocFind d k`: look up key `k` in an association list, returning the first
    matching value or `none`. Frozen helper. -/
def assocFind {α : Type} (d : List (Nat × α)) (k : Nat) : Option α :=
  match d with
  | [] => none
  | (k', v) :: rest => if k' = k then some v else assocFind rest k

/-- `step m st sym`: the destination of the transition from state `st` on
    symbol `sym`, or `st` itself when the map has no entry (a benign default;
    well-formed FSMs always have an entry). Frozen helper mirroring
    `map[state][symbol]`. -/
def step (m : Fsm) (st sym : Nat) : Nat :=
  match assocFind m.trans st with
  | none => st
  | some row => (assocFind row sym).getD st

/-- `runFrom m st s`: fold the transition map from state `st` over the string
    `s`. Frozen helper — the deterministic left-to-right run that underlies
    `accepts`. -/
def runFrom (m : Fsm) : Nat → List Nat → Nat
  | st, [] => st
  | st, c :: cs => runFrom m (step m st c) cs

/-- `insSorted x xs`: insert `x` into the ascending, duplicate-free list `xs`,
    dropping duplicates. Frozen helper — the ordered-set insertion. -/
def insSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x = y then y :: ys
               else if x < y then x :: y :: ys
               else y :: insSorted x ys

/-- `sortDedup xs`: the ascending, duplicate-free canonical form of `xs`.
    Frozen helper — the canonical representation of a finite set of `Nat`, used
    to give crawl meta-states a unique comparable form. -/
def sortDedup (xs : List Nat) : List Nat :=
  xs.foldr insSorted []

/-- `sortNats xs`: ascending sort of a `Nat` list (keeps duplicates). Frozen
    helper for iterating the alphabet in sorted order. -/
def sortNats (xs : List Nat) : List Nat :=
  xs.foldr insSorted []   -- alphabet is already dedup; reuse the sorted insert

/-- `indexOfAux xs y i`: the position of the first element of `xs` equal to `y`,
    starting the count at `i`, or `xs.length + i` if absent. Frozen helper. -/
def indexOfAux (y : List Nat) : List (List Nat) → Nat → Nat
  | [], i => i
  | x :: xs, i => if x = y then i else indexOfAux y xs (i + 1)

/-!
`crawl` is the universal FSM builder, ported from greenery's `crawl`. It does a
breadth-first exploration of an abstract *meta-state* space:

- meta-states are canonicalized to ascending, duplicate-free `List Nat` (a
  reachable subset of the underlying state space);
- `initial` is the starting meta-state;
- `isFinal ms` decides whether meta-state `ms` is accepting;
- `follow ms sym` gives the successor meta-state under `sym`.

New meta-states are appended in first-discovery order and relabeled `0 … n-1`;
transitions are recorded over the *sorted* alphabet. This deterministic BFS
relabeling is exactly what makes the resulting automaton byte-canonical.
-/

/-- `crawlLoop`: the fuel-bounded worklist body of `crawl`. `disc` is the list
    of discovered meta-states in order; `idx` is the next index to process;
    `finsAcc` / `transAcc` accumulate the finals and the transition map. The
    explicit `fuel : Nat` decrements structurally on every processed meta-state,
    so this is a total, terminating `def` (no `partial`): `crawl` supplies a fuel
    that is a genuine upper bound on the number of reachable meta-states, so the
    loop always exits through the `idx ≥ disc.length` branch before the fuel is
    exhausted. Frozen helper. -/
def crawlLoop
    (alpha : List Nat)
    (isFinal : List Nat → Bool)
    (follow : List Nat → Nat → List Nat) :
    Nat → List (List Nat) → Nat → List Nat → List (Nat × List (Nat × Nat)) →
      (List (List Nat) × List Nat × List (Nat × List (Nat × Nat)))
  | 0, disc, _, finsAcc, transAcc => (disc, finsAcc, transAcc)
  | fuel + 1, disc, idx, finsAcc, transAcc =>
    if idx < disc.length then
      let state := disc[idx]!
      let finsAcc := if isFinal state then finsAcc ++ [idx] else finsAcc
      -- build this state's row and grow `disc` with any newly seen meta-states
      let rec go (syms : List Nat) (d : List (List Nat)) (row : List (Nat × Nat)) :
          (List (List Nat) × List (Nat × Nat)) :=
        match syms with
        | [] => (d, row)
        | sym :: rest =>
          let nxt := follow state sym
          let j := indexOfAux nxt d 0
          let d := if j < d.length then d else d ++ [nxt]
          go rest d (row ++ [(sym, j)])
      let (disc, row) := go alpha disc []
      crawlLoop alpha isFinal follow fuel disc (idx + 1) finsAcc (transAcc ++ [(idx, row)])
    else
      (disc, finsAcc, transAcc)

/-- `crawl fuel alpha initial isFinal follow`: build the canonical FSM discovered
    by breadth-first exploration from meta-state `initial`. States are the indices
    `0 … n-1` in first-discovery order; the alphabet is `alpha` sorted. `fuel` must
    be an upper bound on the number of reachable meta-states (each caller passes a
    bound derived from its underlying state space — e.g. `2 ^ |states|` for the
    subset construction in `reversed`, `|states| + 1` for the single-substate
    constructions). Frozen engine mirroring greenery's `crawl`. -/
def crawl
    (fuel : Nat)
    (alpha : List Nat)
    (initial : List Nat)
    (isFinal : List Nat → Bool)
    (follow : List Nat → Nat → List Nat) : Fsm :=
  let alpha := sortNats alpha
  let init := sortDedup initial
  let (disc, fins, tr) := crawlLoop alpha isFinal follow fuel [init] 0 [] []
  { alphabet := alpha
    states   := List.range disc.length
    initial  := 0
    finals   := fins
    trans    := tr }

end Greenery
-- !benchmark @end global_aux

namespace Greenery

-- !benchmark @start code_aux def=accepts
-- !benchmark @end code_aux def=accepts

def accepts : AcceptsSig :=
-- !benchmark @start code def=accepts
  fun m s => m.finals.contains (runFrom m m.initial s)
-- !benchmark @end code def=accepts

-- !benchmark @start code_aux def=reversed
/-- `preimages m sym target`: every state `p` whose `sym`-transition lands in the
    meta-state `target` — the reverse-image used by the subset construction.
    Frozen helper for `reversed`. -/
def preimages (m : Fsm) (sym : Nat) (target : List Nat) : List Nat :=
  sortDedup (m.states.filter (fun p => target.contains (step m p sym)))
-- !benchmark @end code_aux def=reversed

def reversed : ReversedSig :=
-- !benchmark @start code def=reversed
  fun m =>
    -- meta-states are subsets of `m.states`, so `2 ^ |states|` bounds the count.
    crawl (2 ^ m.states.length) m.alphabet (sortDedup m.finals)
      (fun ms => ms.contains m.initial)
      (fun ms sym => preimages m sym ms)
-- !benchmark @end code def=reversed

-- !benchmark @start code_aux def=reduce
-- !benchmark @end code_aux def=reduce

def reduce : ReduceSig :=
-- !benchmark @start code def=reduce
  fun m => reversed (reversed m)
-- !benchmark @end code def=reduce

end Greenery
