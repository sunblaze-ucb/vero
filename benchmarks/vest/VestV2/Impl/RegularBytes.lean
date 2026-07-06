import VestV2.Impl.Properties

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VestV2.Impl.RegularBytes

Byte-level combinator types for the VestV2 parser/serializer framework.
Defines `Variable` (dynamically-sized byte slices), `Fixed`
(statically-sized byte slices), and `Tail` (consume all remaining
bytes), along with their spec-level parse/serialize functions and
exec-level implementations.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations; the pipeline
replaces them with `sorry` inside the `code` markers before presenting
the benchmark to the LLM.
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────

/-- Combinator for parsing and serializing a dynamically-known number
    of bytes. `n` specifies how many bytes to consume. -/
structure Variable where
  n : Nat

/-- Combinator for parsing and serializing a statically-known number
    of bytes. `n` specifies how many bytes to consume. -/
structure Fixed where
  n : Nat

/-- Combinator that consumes all remaining bytes from the input. -/
structure Tail

-- ── Spec helpers (no markers — fixed vocabulary) ──────────

/-- Spec parse for Variable: take exactly `c.n` bytes if available. -/
def Variable.spec_parse (c : Variable) (s : List UInt8) : Option (Int × List UInt8) :=
  if c.n ≤ s.length then
    some (c.n, s.take c.n)
  else
    none

/-- Spec serialize for Variable: identity on the byte slice. -/
def Variable.spec_serialize (_ : Variable) (v : List UInt8) : List UInt8 :=
  v

/-- Spec parse for Fixed: take exactly `c.n` bytes if available. -/
def Fixed.spec_parse (c : Fixed) (s : List UInt8) : Option (Int × List UInt8) :=
  if c.n ≤ s.length then
    some (c.n, s.take c.n)
  else
    none

/-- Spec serialize for Fixed: identity on the byte slice. -/
def Fixed.spec_serialize (_ : Fixed) (v : List UInt8) : List UInt8 :=
  v

/-- Spec parse for Tail: consume all remaining bytes. -/
def Tail.spec_parse (_ : Tail) (s : List UInt8) : Option (Int × List UInt8) :=
  some (s.length, s)

/-- Spec serialize for Tail: identity on the byte slice. -/
def Tail.spec_serialize (_ : Tail) (v : List UInt8) : List UInt8 :=
  v

namespace VestV2

-- ── API signatures (DO NOT MODIFY) ───────────────────────

/-- Parse exactly `c.n` bytes from the input; succeeds iff at least
    `c.n` bytes remain. -/
abbrev VariableParseSig := Variable → List UInt8 → Except ParseError (Nat × List UInt8)

/-- Serialize a byte slice (of length `c.n`) into buf at pos; returns
    number of bytes written. -/
abbrev VariableSerializeSig := Variable → List UInt8 → List UInt8 → Nat → Except SerializeError Nat

/-- Parse exactly `c.n` bytes from the input using the Fixed
    combinator. -/
abbrev FixedParseSig := Fixed → List UInt8 → Except ParseError (Nat × List UInt8)

/-- Serialize a byte slice into buf at pos using the Fixed combinator;
    returns bytes written. -/
abbrev FixedSerializeSig := Fixed → List UInt8 → List UInt8 → Nat → Except SerializeError Nat

/-- Parse all remaining bytes from the input; always succeeds,
    consuming everything. -/
abbrev TailParseSig := List UInt8 → Except ParseError (Nat × List UInt8)

/-- Serialize a byte slice (the tail value) into buf at pos; returns
    bytes written. -/
abbrev TailSerializeSig := List UInt8 → List UInt8 → Nat → Except SerializeError Nat

end VestV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ────────────────────────

-- !benchmark @start code_aux def=variableParse
-- !benchmark @end code_aux def=variableParse

def VestV2.variableParse : VestV2.VariableParseSig :=
-- !benchmark @start code def=variableParse
  fun c s =>
    if c.n ≤ s.length then
      Except.ok (c.n, s.take c.n)
    else
      Except.error ParseError.UnexpectedEndOfInput
-- !benchmark @end code def=variableParse

-- !benchmark @start code_aux def=variableSerialize
-- !benchmark @end code_aux def=variableSerialize

def VestV2.variableSerialize : VestV2.VariableSerializeSig :=
-- !benchmark @start code def=variableSerialize
  fun c v buf pos =>
    if pos + v.length ≤ buf.length then
      Except.ok c.n
    else
      Except.error SerializeError.InsufficientBuffer
-- !benchmark @end code def=variableSerialize

-- !benchmark @start code_aux def=fixedParse
-- !benchmark @end code_aux def=fixedParse

def VestV2.fixedParse : VestV2.FixedParseSig :=
-- !benchmark @start code def=fixedParse
  fun c s =>
    if c.n ≤ s.length then
      Except.ok (c.n, s.take c.n)
    else
      Except.error ParseError.UnexpectedEndOfInput
-- !benchmark @end code def=fixedParse

-- !benchmark @start code_aux def=fixedSerialize
-- !benchmark @end code_aux def=fixedSerialize

def VestV2.fixedSerialize : VestV2.FixedSerializeSig :=
-- !benchmark @start code def=fixedSerialize
  fun c v buf pos =>
    if pos + v.length ≤ buf.length then
      Except.ok c.n
    else
      Except.error SerializeError.InsufficientBuffer
-- !benchmark @end code def=fixedSerialize

-- !benchmark @start code_aux def=tailParse
-- !benchmark @end code_aux def=tailParse

def VestV2.tailParse : VestV2.TailParseSig :=
-- !benchmark @start code def=tailParse
  fun s => Except.ok (s.length, s)
-- !benchmark @end code def=tailParse

-- !benchmark @start code_aux def=tailSerialize
-- !benchmark @end code_aux def=tailSerialize

def VestV2.tailSerialize : VestV2.TailSerializeSig :=
-- !benchmark @start code def=tailSerialize
  fun v buf pos =>
    if pos + v.length ≤ buf.length then
      Except.ok v.length
    else
      Except.error SerializeError.InsufficientBuffer
-- !benchmark @end code def=tailSerialize
