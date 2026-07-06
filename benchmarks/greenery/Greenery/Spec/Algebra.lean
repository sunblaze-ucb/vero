import Greenery.Spec.Fsm

/-!
# Greenery.Spec.Algebra

Specifications for the Boolean algebra on regular languages: `fsmUnion`,
`fsmInter`, `everythingbut` (complement), and `equivalent` (language equality).

The union / intersection / complement laws are stated *semantically* through the
frozen `accepts` fold: for well-formed machines over a shared alphabet, the
combined machine accepts a string iff the Boolean combination of the components'
acceptances holds. This captures the product-automaton semantics soundly without
reasoning about the canonical relabeling. The headline cross-API laws are De
Morgan (`~(A ∪ B) ≡ ~A ∩ ~B`) and the double-complement involution
(`~~A ≡ A`), plus the crown characterization of `equivalent` via the canonical
form (`equivalent A B` iff `reduce A = reduce B`).

`WF` and `sameLang` are the frozen predicates from `Spec/Fsm.lean`; all machines
in the binary laws share one alphabet (greenery unifies alphabets before
combining — here the inputs are pre-shared).

DO NOT MODIFY.
-/

open Greenery

-- ════════════════════════════════════════════════════════════════
-- Union / intersection: product-automaton semantics via accepts
-- ════════════════════════════════════════════════════════════════

/-- Union recognises the union language: for well-formed `a`, `b` over a shared
    alphabet, `fsmUnion a b` accepts a string iff `a` or `b` does —
    `accepts (fsmUnion a b) s = (accepts a s || accepts b s)`. Pins `fsmUnion` to
    the genuine language union (a `fun a _ => a` fails). Over
    `impl.greenery.fsmUnion`, `impl.greenery.accepts`, `WF`. -/
def spec_union_lang (impl : RepoImpl) : Prop :=
  ∀ (a b : Fsm) (s : List Nat), WF a → WF b → a.alphabet = b.alphabet →
    (∀ c ∈ s, a.alphabet.contains c = true) →
    impl.greenery.accepts (impl.greenery.fsmUnion a b) s =
      (impl.greenery.accepts a s || impl.greenery.accepts b s)

/-- Intersection recognises the intersection language: `fsmInter a b` accepts a
    string iff both `a` and `b` do —
    `accepts (fsmInter a b) s = (accepts a s && accepts b s)`. Pins `fsmInter` to
    the genuine language intersection. Over `impl.greenery.fsmInter`,
    `impl.greenery.accepts`, `WF`. -/
def spec_inter_lang (impl : RepoImpl) : Prop :=
  ∀ (a b : Fsm) (s : List Nat), WF a → WF b → a.alphabet = b.alphabet →
    (∀ c ∈ s, a.alphabet.contains c = true) →
    impl.greenery.accepts (impl.greenery.fsmInter a b) s =
      (impl.greenery.accepts a s && impl.greenery.accepts b s)

-- ════════════════════════════════════════════════════════════════
-- Complement: everythingbut
-- ════════════════════════════════════════════════════════════════

/-- Complement recognises the complement language: for a well-formed `m` and any
    string over the alphabet, `everythingbut m` accepts iff `m` does not —
    `accepts (everythingbut m) s = ! accepts m s`. Pins the complement exactly
    (a same-language copy, or a machine that flips finality without completing
    the map, fails). Over `impl.greenery.everythingbut`, `impl.greenery.accepts`,
    `WF`. -/
def spec_complement_lang (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm) (s : List Nat), WF m → (∀ c ∈ s, m.alphabet.contains c = true) →
    impl.greenery.accepts (impl.greenery.everythingbut m) s =
      ! impl.greenery.accepts m s

/-- Double-complement involution (semantic): complementing twice recovers the
    original language — for well-formed `m`, `everythingbut (everythingbut m)`
    accepts exactly what `m` does on every horizon `n`. A cross-API involution
    law. Over `impl.greenery.everythingbut`, `sameLang`, `WF`. -/
def spec_double_complement (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm) (n : Nat), WF m →
    sameLang n m (impl.greenery.everythingbut (impl.greenery.everythingbut m))

-- ════════════════════════════════════════════════════════════════
-- De Morgan: the cross-API crown law
-- ════════════════════════════════════════════════════════════════

/-- De Morgan (semantic): the complement of a union is the intersection of the
    complements — for well-formed `a`, `b` over a shared alphabet,
    `everythingbut (fsmUnion a b)` and `fsmInter (everythingbut a)
    (everythingbut b)` recognise the same language on every horizon `n`. This is
    the headline cross-API algebraic law, tying `everythingbut`, `fsmUnion` and
    `fsmInter` together; it holds only if all three are genuine language
    operations. Over `impl.greenery.everythingbut`, `impl.greenery.fsmUnion`,
    `impl.greenery.fsmInter`, `sameLang`, `WF`. -/
def spec_demorgan (impl : RepoImpl) : Prop :=
  ∀ (a b : Fsm) (n : Nat), WF a → WF b → a.alphabet = b.alphabet →
    sameLang n
      (impl.greenery.everythingbut (impl.greenery.fsmUnion a b))
      (impl.greenery.fsmInter (impl.greenery.everythingbut a) (impl.greenery.everythingbut b))

-- ════════════════════════════════════════════════════════════════
-- equivalent: canonical form decides language equality (crown)
-- ════════════════════════════════════════════════════════════════

/-- `equivalent` is decided by the canonical form: `equivalent a b` is `true`
    exactly when the two reductions are byte-identical —
    `equivalent a b = decide (reduce a = reduce b)`. This is the crown cross-API
    identity. greenery computes `equivalent` as "the symmetric difference `a ^ b`
    recognises nothing" (`(a ^ b).empty()`), a computation *independent* of
    `reduce`; this law asserts that that emptiness test agrees exactly with
    canonical-form equality — two machines recognise the same language iff they
    minimize to literally the same FSM (Myhill–Nerode). Because the two sides are
    computed by genuinely different procedures, the law has real content (it is
    not true by definition). Restricted to well-formed machines over a shared
    alphabet (greenery's domain), so the identity is not diluted by totalized
    behaviour on malformed FSMs. Over `impl.greenery.equivalent`,
    `impl.greenery.reduce`, `WF`. -/
def spec_equivalent_iff_reduce_eq (impl : RepoImpl) : Prop :=
  ∀ (a b : Fsm), WF a → WF b → a.alphabet = b.alphabet →
    impl.greenery.equivalent a b = decide (impl.greenery.reduce a = impl.greenery.reduce b)

/-- `equivalent` is sound for the language: for well-formed machines over a
    shared alphabet, if `equivalent a b` is `true` then `a` and `b` accept
    exactly the same strings on every horizon — canonical-form equality implies
    language equality. Together with `spec_equivalent_complete` this pins
    `equivalent` to genuine language equality. Over `impl.greenery.equivalent`,
    `sameLang`, `WF`. -/
def spec_equivalent_sound (impl : RepoImpl) : Prop :=
  ∀ (a b : Fsm) (n : Nat), WF a → WF b → a.alphabet = b.alphabet →
    impl.greenery.equivalent a b = true → sameLang n a b

/-- `equivalent` is complete for the language: for well-formed machines over a
    shared alphabet, if `a` and `b` recognise the same language (agree on
    `accepts` for **all** strings) then `equivalent a b` is `true`. The converse
    of `spec_equivalent_sound`; together they characterize `equivalent` as exact
    language equality — the decision procedure neither over- nor under-reports.
    Over `impl.greenery.equivalent`, `sameLang`, `WF`. -/
def spec_equivalent_complete (impl : RepoImpl) : Prop :=
  ∀ (a b : Fsm), WF a → WF b → a.alphabet = b.alphabet →
    (∀ n, sameLang n a b) → impl.greenery.equivalent a b = true

-- ════════════════════════════════════════════════════════════════
-- Additional cross-API algebraic laws (canonical-form pressure)
-- ════════════════════════════════════════════════════════════════

/-- Dual De Morgan (semantic): the complement of an intersection is the union of
    the complements — for well-formed `a`, `b` over a shared alphabet,
    `everythingbut (fsmInter a b)` and `fsmUnion (everythingbut a)
    (everythingbut b)` recognise the same language on every horizon `n`. The
    companion to `spec_demorgan`, closing the Boolean-algebra duality. Over
    `impl.greenery.everythingbut`, `impl.greenery.fsmInter`,
    `impl.greenery.fsmUnion`, `sameLang`, `WF`. -/
def spec_demorgan_dual (impl : RepoImpl) : Prop :=
  ∀ (a b : Fsm) (n : Nat), WF a → WF b → a.alphabet = b.alphabet →
    sameLang n
      (impl.greenery.everythingbut (impl.greenery.fsmInter a b))
      (impl.greenery.fsmUnion (impl.greenery.everythingbut a) (impl.greenery.everythingbut b))

/-- Union commutativity as canonical-form equality: for well-formed `a`, `b`
    over a shared alphabet, `reduce (fsmUnion a b) = reduce (fsmUnion b a)` —
    the two orderings minimize to the *byte-identical* FSM. A canonical-form law
    (stronger than mere language equality): it exercises both that `fsmUnion` is
    commutative up to language and that `reduce` is a genuine canonical form.
    Over `impl.greenery.reduce`, `impl.greenery.fsmUnion`, `WF`. -/
def spec_union_comm (impl : RepoImpl) : Prop :=
  ∀ (a b : Fsm), WF a → WF b → a.alphabet = b.alphabet →
    impl.greenery.reduce (impl.greenery.fsmUnion a b) =
      impl.greenery.reduce (impl.greenery.fsmUnion b a)

/-- Union idempotence as canonical-form equality: for a well-formed `a`,
    `reduce (fsmUnion a a) = reduce a` — a language union with itself minimizes
    to the same canonical FSM as `a`. Pins `fsmUnion` against absorbing a
    self-union and `reduce` against distinguishing language-equal machines. Over
    `impl.greenery.reduce`, `impl.greenery.fsmUnion`, `WF`. -/
def spec_union_idempotent (impl : RepoImpl) : Prop :=
  ∀ (a : Fsm), WF a → impl.greenery.reduce (impl.greenery.fsmUnion a a) = impl.greenery.reduce a

-- ════════════════════════════════════════════════════════════════
-- Complement partition + canonical-form contexts (Myhill–Nerode)
-- ════════════════════════════════════════════════════════════════

/-- Complement partitions the string set: for a well-formed `m` and any string
    over its alphabet, `fsmInter m (everythingbut m)` accepts nothing and
    `fsmUnion m (everythingbut m)` accepts everything —
    `accepts (fsmInter m (~m)) s = false` and `accepts (fsmUnion m (~m)) s =
    true`. Ties `everythingbut`, `fsmInter`, `fsmUnion` together as a genuine
    Boolean complement (law of contradiction and excluded middle over the full
    string set). Over `impl.greenery.fsmInter`, `impl.greenery.fsmUnion`,
    `impl.greenery.everythingbut`, `impl.greenery.accepts`, `symbolsIn`,
    `WF`. -/
def spec_complement_partition_full (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm) (s : List Nat), WF m → symbolsIn m.alphabet s →
    impl.greenery.accepts (impl.greenery.fsmInter m (impl.greenery.everythingbut m)) s = false ∧
    impl.greenery.accepts (impl.greenery.fsmUnion m (impl.greenery.everythingbut m)) s = true

/-- Complement preserves the minimal state count: for a well-formed `m`, the
    reduced complement has exactly as many states as the reduced original —
    `(reduce (everythingbut m)).states.length = (reduce m).states.length`. A
    language and its complement share the same minimal-DFA size. Over
    `impl.greenery.reduce`, `impl.greenery.everythingbut`, `WF`. -/
def spec_complement_preserves_state_count (impl : RepoImpl) : Prop :=
  ∀ (m : Fsm), WF m →
    (impl.greenery.reduce (impl.greenery.everythingbut m)).states.length =
      (impl.greenery.reduce m).states.length

/-- Equivalence yields identical canonical forms in every Boolean context: for
    well-formed `a`, `b` over a shared alphabet with `equivalent a b = true`, all
    four reductions coincide byte-identically — `reduce a = reduce b`,
    `reduce (everythingbut a) = reduce (everythingbut b)`,
    `reduce (fsmInter a b) = reduce a`, and `reduce (fsmUnion a b) = reduce a`.
    Language equality is a congruence for complement, intersection and union, all
    canonicalized to the same FSM. Over `impl.greenery.equivalent`,
    `impl.greenery.reduce`, `impl.greenery.everythingbut`,
    `impl.greenery.fsmInter`, `impl.greenery.fsmUnion`, `WF`. -/
def spec_equivalent_normal_form_contexts (impl : RepoImpl) : Prop :=
  ∀ (a b : Fsm), WF a → WF b → a.alphabet = b.alphabet →
    impl.greenery.equivalent a b = true →
      impl.greenery.reduce a = impl.greenery.reduce b ∧
      impl.greenery.reduce (impl.greenery.everythingbut a) =
        impl.greenery.reduce (impl.greenery.everythingbut b) ∧
      impl.greenery.reduce (impl.greenery.fsmInter a b) = impl.greenery.reduce a ∧
      impl.greenery.reduce (impl.greenery.fsmUnion a b) = impl.greenery.reduce a
