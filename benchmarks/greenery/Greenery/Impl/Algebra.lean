import Greenery.Impl.Fsm

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Greenery.Impl.Algebra

Boolean algebra on regular languages, ported from `greenery/fsm.py`: `fsmUnion`
(`|`), `fsmInter` (`&`), `everythingbut` (complement `~`), and the language-
equality decision `equivalent`.

`fsmUnion` / `fsmInter` are built by `parallel`: a product-automaton `crawl`
whose meta-state is the pair of substates, with finality determined by a
combiner over the substate-finality vector (`any` for union, `all` for
intersection) — the result is then `reduce`d to byte-canonical form.
`everythingbut` `crawl`s the same state space with inverted finality (then
`reduce`s). `equivalent A B` is greenery's `==`: `A` and `B` recognise the same
language, decided by canonical form — `reduce A = reduce B`.

All functions share a single fixed alphabet across their inputs (greenery
unifies alphabets before combining; here the inputs are pre-shared). All are
total, terminating `def`s; no `Float`.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Greenery

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `fsmUnion a b`: an FSM recognising the union of the languages of `a`, `b`. -/
abbrev FsmUnionSig := Fsm → Fsm → Fsm

/-- `fsmInter a b`: an FSM recognising the intersection of the languages. -/
abbrev FsmInterSig := Fsm → Fsm → Fsm

/-- `everythingbut a`: an FSM recognising the complement of `a`'s language. -/
abbrev EverythingButSig := Fsm → Fsm

/-- `equivalent a b`: do `a` and `b` recognise the same language? -/
abbrev EquivalentSig := Fsm → Fsm → Bool

end Greenery

-- !benchmark @start global_aux
namespace Greenery

/-- `encodePair x y`: a bijective `Nat` pairing (Cantor) so a product meta-state
    `(x, y)` can be represented as a single `Nat` inside crawl's meta-state
    lists. Frozen helper. -/
def encodePair (x y : Nat) : Nat :=
  (x + y) * (x + y + 1) / 2 + y

/-- `parallel a b combine`: the product-automaton `crawl` of `a` and `b`. A
    meta-state is the singleton `[encodePair sa sb]` of the current substate
    pair; it is final iff `combine` accepts the pair of substate-finality flags.
    The result is `reduce`d to canonical form. Frozen engine mirroring
    greenery's `parallel`. -/
def parallel (a b : Fsm) (combine : Bool → Bool → Bool) : Fsm :=
  -- meta-states are single encoded pairs from `a.states × b.states`, so the
  -- product size (+1 for the initial default) bounds the reachable count.
  reduce (crawl (a.states.length * b.states.length + 1)
    a.alphabet [encodePair a.initial b.initial]
    (fun ms =>
      match ms with
      | [code] =>
        -- decode is unnecessary: we track the pair via the follow closure below
        -- but crawl only hands us the canonical code list, so recompute finality
        -- from the code by scanning both state spaces.
        decodeFinal a b combine code
      | _ => false)
    (fun ms sym =>
      match ms with
      | [code] => [stepPair a b code sym]
      | _ => ms))
where
  /-- decode a paired code back to `(sa, sb)` by searching the product space. -/
  decodePair (a b : Fsm) (code : Nat) : (Nat × Nat) :=
    let cands := a.states.flatMap (fun sa => b.states.map (fun sb => (sa, sb)))
    (cands.find? (fun p => encodePair p.1 p.2 = code)).getD (a.initial, b.initial)
  decodeFinal (a b : Fsm) (combine : Bool → Bool → Bool) (code : Nat) : Bool :=
    let (sa, sb) := decodePair a b code
    combine (a.finals.contains sa) (b.finals.contains sb)
  stepPair (a b : Fsm) (code sym : Nat) : Nat :=
    let (sa, sb) := decodePair a b code
    encodePair (step a sa sym) (step b sb sym)

/-- `reachAux m fuel frontier seen`: fuel-bounded breadth-first accumulation of
    the states reachable from `frontier` in `m`. Frozen helper for `isLive`. -/
def reachAux (m : Fsm) : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _, [], seen => seen
  | fuel + 1, st :: rest, seen =>
    if seen.contains st then reachAux m (fuel + 1) rest seen
    else
      let nexts := m.alphabet.map (fun sym => step m st sym)
      reachAux m fuel (rest ++ nexts) (seen ++ [st])

/-- `isLive m st`: can a final state be reached from `st`? Frozen helper
    mirroring greenery's `islive` (BFS over the reachable set, bounded by the
    number of states). -/
def isLive (m : Fsm) (st : Nat) : Bool :=
  (reachAux m (m.states.length + 1) [st] []).any (fun s => m.finals.contains s)

/-- `fsmEmpty m`: does `m` recognise NO strings? Frozen helper mirroring
    greenery's `empty` — the initial state is not live. -/
def fsmEmpty (m : Fsm) : Bool :=
  ! isLive m m.initial

/-- `symDiff a b`: the symmetric-difference automaton — recognises strings
    accepted by exactly one of `a`, `b`. Frozen helper (greenery's `^`). -/
def symDiff (a b : Fsm) : Fsm :=
  parallel a b (fun x y => xor x y)

end Greenery
-- !benchmark @end global_aux

namespace Greenery

-- !benchmark @start code_aux def=fsmUnion
-- !benchmark @end code_aux def=fsmUnion

def fsmUnion : FsmUnionSig :=
-- !benchmark @start code def=fsmUnion
  fun a b => parallel a b (· || ·)
-- !benchmark @end code def=fsmUnion

-- !benchmark @start code_aux def=fsmInter
-- !benchmark @end code_aux def=fsmInter

def fsmInter : FsmInterSig :=
-- !benchmark @start code def=fsmInter
  fun a b => parallel a b (· && ·)
-- !benchmark @end code def=fsmInter

-- !benchmark @start code_aux def=everythingbut
-- !benchmark @end code_aux def=everythingbut

def everythingbut : EverythingButSig :=
-- !benchmark @start code def=everythingbut
  fun m =>
    -- meta-states are single substates of `m`, so `|states| + 1` bounds the count.
    reduce (crawl (m.states.length + 1) m.alphabet [m.initial]
      (fun ms => match ms with
        | [st] => ! m.finals.contains st
        | _ => false)
      (fun ms sym => match ms with
        | [st] => [step m st sym]
        | _ => ms))
-- !benchmark @end code def=everythingbut

-- !benchmark @start code_aux def=equivalent
-- !benchmark @end code_aux def=equivalent

def equivalent : EquivalentSig :=
-- !benchmark @start code def=equivalent
  fun a b => fsmEmpty (symDiff a b)
-- !benchmark @end code def=equivalent

end Greenery
