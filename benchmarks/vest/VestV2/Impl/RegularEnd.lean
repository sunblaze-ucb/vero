import VestV2.Impl.Properties

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VestV2.Impl.RegularEnd

End combinator for the VestV2 parser/serializer framework.
Succeeds only when the input buffer is empty and consumes nothing.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
Implement only the function bodies.
-/

-- ── Types (no markers — fixed vocabulary) ─────────────

/-- Combinator that succeeds only at the end of the input buffer. -/
structure End where
  deriving Inhabited

-- ── Spec helpers (no markers — fixed vocabulary) ──────────

namespace End

/-- Specification of parse for End: succeeds with (0, ()) iff input is empty. -/
def spec_parse (_ : End) (s : List UInt8) : Option (Int × Unit) :=
  match s with
  | [] => some (0, ())
  | _ :: _ => none

/-- Specification of serialize for End: always produces empty bytes. -/
def spec_serialize (_ : End) (_ : Unit) : List UInt8 :=
  []

end End

namespace VestV2

-- ── API signatures (DO NOT MODIFY) ───────────────────────

/-- Parse the End combinator: succeeds returning (0, ()) iff the input
    is empty, otherwise returns ParseError.NotEof. -/
abbrev EndParseSig := List UInt8 → Except ParseError (Nat × Unit)

/-- Serialize the End combinator: always succeeds returning 0 bytes written. -/
abbrev EndSerializeSig := Unit → List UInt8 → Nat → Except SerializeError Nat

end VestV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ────────────────────

-- !benchmark @start code_aux def=endParse
-- !benchmark @end code_aux def=endParse

def VestV2.endParse : VestV2.EndParseSig :=
-- !benchmark @start code def=endParse
  fun s =>
    match s with
    | [] => Except.ok (0, ())
    | _ :: _ => Except.error ParseError.NotEof
-- !benchmark @end code def=endParse

-- !benchmark @start code_aux def=endSerialize
-- !benchmark @end code_aux def=endSerialize

def VestV2.endSerialize : VestV2.EndSerializeSig :=
-- !benchmark @start code def=endSerialize
  fun _v _buf _pos =>
    Except.ok 0
-- !benchmark @end code def=endSerialize
