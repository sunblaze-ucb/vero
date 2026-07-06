import VestV2.Impl.Properties

/-!
# VestV2.Impl.RegularRepetition

Repetition combinators for the VestV2 framework. `RepeatN` applies an
inner combinator exactly `n` times in sequence; `Repeat` applies it
until parsing fails; `RepeatResult` is the list of parsed values.

Types and spec helpers are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────

/-- Repeat the inner combinator exactly `n` times. -/
structure RepeatN (Inner : Type) where
  inner : Inner
  n : Nat

/-- Repeat the inner combinator until it fails. -/
structure Repeat (Inner : Type) where
  inner : Inner

/-- Result of a repetition: a list of parsed values. -/
abbrev RepeatResult (T : Type) := List T

-- ── Spec helpers (no markers — fixed vocabulary) ──────────

/-- Spec parse for RepeatN: apply the inner combinator exactly n times
    in sequence, accumulating results into a list. -/
def RepeatN.spec_parse {Inner T : Type} [SpecCombinator Inner T] (c : RepeatN Inner) :
    List UInt8 → Option (Int × List T) := fun s =>
  let rec go : Nat → List UInt8 → Int → List T → Option (Int × List T)
    | 0, _, acc_n, acc_v => some (acc_n, acc_v)
    | k+1, s', acc_n, acc_v =>
      match SpecCombinator.spec_parse c.inner s' with
      | none => none
      | some (n, v) => go k (s'.drop n.toNat) (acc_n + n) (acc_v ++ [v])
  go c.n s 0 []
