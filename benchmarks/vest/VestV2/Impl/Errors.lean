-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VestV2.Impl.Errors

Core error types for the VestV2 parser/serializer combinator library.
Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations; the pipeline
replaces them with `sorry` inside the `code` markers before presenting
the benchmark to the LLM.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- Parser errors. -/
inductive ParseError where
  | AndThenUnusedBytes
  | UnexpectedEndOfInput
  | OrdChoiceNoMatch
  | CondFailed
  | TryMapFailed
  | RefinedPredicateFailed
  | NotEof
  | Other (_ : String)
  deriving Repr, DecidableEq, BEq

/-- Serializer errors. -/
inductive SerializeError where
  | InsufficientBuffer
  | Other (_ : String)
  deriving Repr, DecidableEq, BEq

/-- Sum of both parse and serialize errors. -/
inductive Error where
  | Parse (_ : ParseError)
  | Serialize (_ : SerializeError)
  deriving Repr, DecidableEq, BEq

namespace VestV2

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

abbrev FromParseErrorSig := ParseError → Error
abbrev FromSerializeErrorSig := SerializeError → Error

end VestV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=fromParseError
-- !benchmark @end code_aux def=fromParseError

def VestV2.fromParseError : VestV2.FromParseErrorSig :=
-- !benchmark @start code def=fromParseError
  fun e => Error.Parse e
-- !benchmark @end code def=fromParseError

-- !benchmark @start code_aux def=fromSerializeError
-- !benchmark @end code_aux def=fromSerializeError

def VestV2.fromSerializeError : VestV2.FromSerializeErrorSig :=
-- !benchmark @start code def=fromSerializeError
  fun e => Error.Serialize e
-- !benchmark @end code def=fromSerializeError
