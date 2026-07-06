/-!
# Dafnycrypto.Impl.Util.Option

Option type alias and extraction helpers matching the Dafny `Optional` module.
Types and helpers are fixed vocabulary — DO NOT MODIFY.
-/

-- ── Core type alias (DO NOT MODIFY) ────────────────────────────────────────────

/-- Lean's built-in `Option α`; aliased for naming parity with the Dafny source. -/
abbrev DafnyCrypto.DCOption (α : Type) := Option α

-- ── API helpers (fully defined, not LLM tasks) ─────────────────────────────────

/-- Extract the value from a `some` option, given a proof that it is `some`. -/
def DafnyCrypto.unwrap {α : Type} (o : Option α) (h : o.isSome = true) : α :=
  o.get h

/-- Return the contained value, or the given default if `none`. -/
def DafnyCrypto.unwrapOr {α : Type} (o : Option α) (default : α) : α :=
  o.getD default
