import Base58.Impl.Codec
import Base58.Bundle
import Base58.Harness
import Base58.Spec.Codec
import Base58.Test

/-!
# Base58

Root import hub for the base58 codec benchmark: a positional numeral system in
radix 58 over a fixed 58-character alphabet (omitting `0`, `O`, `I`, `l`). Four
codec operations: `decodeInt`/`encodeInt` (integer ↔ numeral) and
`encode`/`decode` (bytes ↔ numeral). Integers are unbounded `Nat`, bytes are
`Nat` in `0…255` carried in a `List Nat`, the encoded form is a `String`.
Behaviour is pinned by `Spec/Codec.lean`.
-/
