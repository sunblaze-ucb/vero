import VestV2.Impl.Properties

/-!
# VestV2.Impl.RegularSequence

Sequential combinator types for the VestV2 parser/serializer framework.
Defines Pair (dependent and non-dependent), Preceded, Terminated combinators,
and supporting types (GhostFn, POrSType, Continuation).

Types are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Types (no markers — fixed vocabulary) ────────────────────

/-- Wraps a pure function, used as the spec-level continuation for
    dependent pair combinators. -/
structure GhostFn (A B : Type) where
  f : A → B

/-- Non-dependent pair combinator at the spec level: sequentially
    applies `fst` then `snd`. -/
structure SpecPair (Fst Snd : Type) where
  fst : Fst
  snd : Snd

/-- Dependent pair combinator: sequentially applies `fst`, then a
    continuation-selected `snd` combinator. -/
structure Pair (Fst Snd : Type) where
  fst : Fst
  snd : Snd

/-- Tagged union distinguishing parse-time vs serialize-time values.
    Used for Pair's continuation dispatch. -/
inductive POrSType (P S : Type) where
  | parse : P → POrSType P S
  | serialize : S → POrSType P S

/-- Sequential combinator that returns only the second result. -/
structure Preceded (Fst Snd : Type) where
  fst : Fst
  snd : Snd

/-- Sequential combinator that returns only the first result. -/
structure Terminated (Fst Snd : Type) where
  fst : Fst
  snd : Snd

/-- Continuation: wraps a function from Input to Output. -/
structure Continuation (Input Output : Type) where
  apply : Input → Output

-- ── Spec helpers (no markers — spec vocabulary) ──────────────

namespace SpecPair

/-- Specification-level parse for a non-dependent pair combinator.
    Parses `fst` from the buffer, then `snd` from the remainder. -/
def spec_parse {F S A B : Type} [SpecCombinator F A] [SpecCombinator S B]
    (c : SpecPair F S) (s : List UInt8) : Option (Int × (A × B)) :=
  match SpecCombinator.spec_parse c.fst s with
  | some (n, v1) =>
    match SpecCombinator.spec_parse c.snd (s.drop n.toNat) with
    | some (m, v2) => some (n + m, (v1, v2))
    | none => none
  | none => none

/-- Specification-level serialize for a non-dependent pair combinator.
    Serializes both components and concatenates. -/
def spec_serialize {F S A B : Type} [SpecCombinator F A] [SpecCombinator S B]
    (c : SpecPair F S) (v : A × B) : List UInt8 :=
  SpecCombinator.spec_serialize c.fst v.1 ++ SpecCombinator.spec_serialize c.snd v.2

end SpecPair
