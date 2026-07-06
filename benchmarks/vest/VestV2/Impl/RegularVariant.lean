import VestV2.Impl.Properties

/-!
# VestV2.Impl.RegularVariant

Variant (choice/optional) combinator types for the VestV2 parser/serializer
framework. Defines `Either`, `Choice`, `Opt`, `Optional`, and `OptThen`
types with their spec-level parse and serialize functions.

Types and spec-helper function bodies are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────

/-- Sum type for the result of ordered-choice parsing. -/
inductive Either (L R : Type) where
  | Left : L → Either L R
  | Right : R → Either L R

/-- Ordered-choice combinator: tries `fst`, then `snd` on failure. -/
structure Choice (Fst Snd : Type) where
  fst : Fst
  snd : Snd

/-- Optional combinator that never fails. If inner fails, returns `none`. -/
structure Opt (Inner : Type) where
  inner : Inner

/-- Wrapper for optional parse results. -/
structure Optional (Inner : Type) where
  inner : Inner

/-- Optional-then combinator: tries `cond` optionally, then `inner`. -/
structure OptThen (Cond Inner : Type) where
  cond : Cond
  inner : Inner


def Choice.spec_parse {F S A B : Type} [SpecCombinator F A] [SpecCombinator S B]
    (c : Choice F S) (s : List UInt8) : Option (Int × Either A B) :=
  match SpecCombinator.spec_parse c.fst s with
  | some (n, v) => some (n, Either.Left v)
  | none =>
    match SpecCombinator.spec_parse c.snd s with
    | some (n, v) => some (n, Either.Right v)
    | none => none

def Choice.spec_serialize {F S A B : Type} [SpecCombinator F A] [SpecCombinator S B]
    (c : Choice F S) (v : Either A B) : List UInt8 :=
  match v with
  | Either.Left v => SpecCombinator.spec_serialize c.fst v
  | Either.Right v => SpecCombinator.spec_serialize c.snd v

def Opt.spec_parse {T A : Type} [SpecCombinator T A]
    (o : Opt T) (s : List UInt8) : Option (Int × Option A) :=
  match SpecCombinator.spec_parse o.inner s with
  | some (n, v) => some (n, some v)
  | none => some (0, none)

def Opt.spec_serialize {T A : Type} [SpecCombinator T A]
    (o : Opt T) (v : Option A) : List UInt8 :=
  match v with
  | some v => SpecCombinator.spec_serialize o.inner v
  | none => []
