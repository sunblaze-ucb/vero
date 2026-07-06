import VestV2.Impl.Errors

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VestV2.Impl.RegularSuccess

Success combinator for the VestV2 parser/serializer framework.
Always succeeds on parse returning (0, ()) and consumes no bytes.
Serialize always returns 0 bytes written.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations.
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────

/-- Combinator that always succeeds and consumes nothing. -/
structure Success

namespace VestV2

-- ── API signatures (DO NOT MODIFY) ───────────────────────

/-- Parse for the Success combinator: always returns Ok(0, ()),
    consuming no bytes. -/
abbrev SuccessParseSig := List UInt8 → Except ParseError (Nat × Unit)

/-- Serialize for the Success combinator: always returns 0 bytes
    written. -/
abbrev SuccessSerializeSig := Unit → List UInt8 → Nat → Except SerializeError Nat

end VestV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ────────────────────────

-- !benchmark @start code_aux def=successParse
-- !benchmark @end code_aux def=successParse

def VestV2.successParse : VestV2.SuccessParseSig :=
-- !benchmark @start code def=successParse
  fun _s => Except.ok (0, ())
-- !benchmark @end code def=successParse

-- !benchmark @start code_aux def=successSerialize
-- !benchmark @end code_aux def=successSerialize

def VestV2.successSerialize : VestV2.SuccessSerializeSig :=
-- !benchmark @start code def=successSerialize
  fun _v _buf _pos => Except.ok 0
-- !benchmark @end code def=successSerialize
