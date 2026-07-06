import VestV2.Impl.Errors

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VestV2.Impl.RegularFail

Fail combinator for the VestV2 parser/serializer framework.
Always fails on parse (returns `ParseError.OrdChoiceNoMatch`).
Serialize is unreachable in practice and reports an error.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations.
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────

/-- Combinator that always fails on parse. Used for custom error
    messages and as a base case for ordered-choice chains. -/
structure Fail

namespace VestV2

-- ── API signatures (DO NOT MODIFY) ───────────────────────

/-- Parse for the Fail combinator: always returns
    `ParseError.OrdChoiceNoMatch` regardless of input. -/
abbrev FailParseSig := List UInt8 → Except ParseError (Nat × Unit)

/-- Serialize for the Fail combinator: unreachable in practice and always fails. -/
abbrev FailSerializeSig := Unit → List UInt8 → Nat → Except SerializeError Nat

end VestV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ────────────────────────

-- !benchmark @start code_aux def=failParse
-- !benchmark @end code_aux def=failParse

def VestV2.failParse : VestV2.FailParseSig :=
-- !benchmark @start code def=failParse
  fun _s => Except.error ParseError.OrdChoiceNoMatch
-- !benchmark @end code def=failParse

-- !benchmark @start code_aux def=failSerialize
-- !benchmark @end code_aux def=failSerialize

def VestV2.failSerialize : VestV2.FailSerializeSig :=
-- !benchmark @start code def=failSerialize
  fun _v _buf _pos => Except.error (SerializeError.Other "fail")
-- !benchmark @end code def=failSerialize
