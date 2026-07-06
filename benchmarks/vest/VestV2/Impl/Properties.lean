import VestV2.Impl.Errors

/-!
# VestV2.Impl.Properties

Foundation types for the VestV2 combinator framework: result types
(`PResult`, `SResult`) and the combinator type class hierarchy
(`SpecCombinator`, `SecureSpecCombinator`, `Combinator`).

Types are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Result types (DO NOT MODIFY) ────────────────────────

/-- The parse result of a combinator: either an error or a pair of
    (bytes consumed, parsed value). -/
abbrev PResult (T E : Type) := Except E (Nat × T)

/-- The serialize result of a combinator: either an error or the value. -/
abbrev SResult (T E : Type) := Except E T

-- ── Combinator type class hierarchy (DO NOT MODIFY) ─────

/-- Specification for parser and serializer combinators. All VestV2
    combinators must implement this class. -/
class SpecCombinator (Self : Type) (T : outParam Type) where
  /-- Well-formedness of the format type. -/
  wf : Self → T → Bool := fun _ _ => true
  /-- Pre-conditions for parsing and serialization. -/
  requires : Self → Bool := fun _ => true
  /-- The specification of parse. -/
  spec_parse : Self → List UInt8 → Option (Int × T)
  /-- The specification of serialize. -/
  spec_serialize : Self → T → List UInt8

/-- Security properties and lemma obligations for combinators. -/
class SecureSpecCombinator (Self : Type) (T : outParam Type)
    extends SpecCombinator Self T where
  /-- Whether the combinator is prefix-secure. -/
  is_prefix_secure : Bool
  /-- Whether the combinator is productive. -/
  is_productive : Self → Bool

/-- Executable implementation for parser and serializer combinators. -/
class Combinator (Self : Type) (T : outParam Type)
    extends SecureSpecCombinator Self T where
  /-- The parsing function. -/
  parse : Self → List UInt8 → Except ParseError (Nat × T)
  /-- The serialization function. -/
  serialize : Self → T → List UInt8 → Nat → Except SerializeError Nat

-- ── Spec helpers (DO NOT MODIFY) ────────────────────────

/-- Splice bytes `v` into `data` at position `pos`, overwriting
    `v.length` bytes; used in serialize postconditions. -/
def seq_splice (data : List UInt8) (pos : Nat) (v : List UInt8) : List UInt8 :=
  data.take pos ++ v ++ data.drop (pos + v.length)
