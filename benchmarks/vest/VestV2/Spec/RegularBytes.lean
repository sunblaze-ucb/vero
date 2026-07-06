import VestV2.Impl.RegularBytes
import VestV2.Harness

/-!
# VestV2.Spec.RegularBytes

Specifications for the byte combinator module. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; theorem stubs live
in `VestV2/Proof/RegularBytes.lean`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- For Variable and Fixed, parsing the serialization of a well-formed
    byte list yields the original list; Tail always consumes the whole
    input. -/
def spec_bytes_parse_serialize_roundtrip (_impl : RepoImpl) : Prop :=
  (∀ (c : Variable) (v : List UInt8), v.length = c.n →
    Variable.spec_parse c (Variable.spec_serialize c v) = some ((c.n : Int), v)) ∧
  (∀ (c : Fixed) (v : List UInt8), v.length = c.n →
    Fixed.spec_parse c (Fixed.spec_serialize c v) = some ((c.n : Int), v)) ∧
  (∀ (v : List UInt8),
    Tail.spec_parse Tail.mk (Tail.spec_serialize Tail.mk v) = some ((v.length : Int), v))

/-- For Variable, Fixed, and Tail, parsing a byte buffer and then
    serializing the result returns the consumed prefix. -/
def spec_bytes_serialize_parse_roundtrip (_impl : RepoImpl) : Prop :=
  (∀ (c : Variable) (s : List UInt8), Variable.spec_parse c s = some ((c.n : Int), s.take c.n) →
    Variable.spec_serialize c (s.take c.n) = s.take c.n) ∧
  (∀ (c : Fixed) (s : List UInt8), Fixed.spec_parse c s = some ((c.n : Int), s.take c.n) →
    Fixed.spec_serialize c (s.take c.n) = s.take c.n)

/-- variableParse returns Ok(n, s.take n) iff n ≤ s.length, and
    Err(UnexpectedEndOfInput) otherwise. -/
def spec_variable_parse_correct (impl : RepoImpl) : Prop :=
  ∀ (c : Variable) (s : List UInt8),
  (c.n ≤ s.length → impl.vest.variableParse c s = Except.ok (c.n, s.take c.n)) ∧
  (c.n > s.length → impl.vest.variableParse c s = Except.error ParseError.UnexpectedEndOfInput)

/-- For well-formed Variable inputs, variableSerialize returns the byte
    count on sufficient buffer space and InsufficientBuffer otherwise. -/
def spec_variable_serialize_correct (impl : RepoImpl) : Prop :=
  ∀ (c : Variable) (v buf : List UInt8) (pos : Nat),
  v.length = c.n →
  (pos + v.length ≤ buf.length → impl.vest.variableSerialize c v buf pos = Except.ok c.n) ∧
  (pos + v.length > buf.length → impl.vest.variableSerialize c v buf pos = Except.error SerializeError.InsufficientBuffer)

/-- fixedParse agrees with Fixed.spec_parse on every input buffer. -/
def spec_fixed_parse_correct (impl : RepoImpl) : Prop :=
  ∀ (c : Fixed) (s : List UInt8),
  (c.n ≤ s.length → impl.vest.fixedParse c s = Except.ok (c.n, s.take c.n)) ∧
  (c.n > s.length → impl.vest.fixedParse c s = Except.error ParseError.UnexpectedEndOfInput)

/-- For well-formed Fixed inputs, fixedSerialize returns the byte count
    on sufficient buffer space and InsufficientBuffer otherwise. -/
def spec_fixed_serialize_correct (impl : RepoImpl) : Prop :=
  ∀ (c : Fixed) (v buf : List UInt8) (pos : Nat),
  v.length = c.n →
  (pos + v.length ≤ buf.length → impl.vest.fixedSerialize c v buf pos = Except.ok c.n) ∧
  (pos + v.length > buf.length → impl.vest.fixedSerialize c v buf pos = Except.error SerializeError.InsufficientBuffer)

/-- tailParse always succeeds, consuming and returning the entire input. -/
def spec_tail_parse_correct (impl : RepoImpl) : Prop :=
  ∀ (s : List UInt8), impl.vest.tailParse s = Except.ok (s.length, s)

/-- tailSerialize returns the input length on sufficient buffer space
    and InsufficientBuffer otherwise. -/
def spec_tail_serialize_correct (impl : RepoImpl) : Prop :=
  ∀ (v buf : List UInt8) (pos : Nat),
  (pos + v.length ≤ buf.length → impl.vest.tailSerialize v buf pos = Except.ok v.length) ∧
  (pos + v.length > buf.length → impl.vest.tailSerialize v buf pos = Except.error SerializeError.InsufficientBuffer)
