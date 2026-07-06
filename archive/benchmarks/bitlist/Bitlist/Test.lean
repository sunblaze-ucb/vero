import Bitlist.Impl.Bitlist
import Bitlist.Harness

/-!
# Bitlist.Test

`#guard` conformance tests. Guards run against the curator's reference
implementations that live INSIDE the `code` markers in `Impl/Bitlist.lean`,
accessed through the `canonical : RepoImpl` instance from `Harness.lean`.
Before the LLM sees the benchmark, pre-agent-gen replaces marker
contents with `sorry` — these guards catch regressions in the
reference implementations themselves.

`Bitlist = List Bool` (big-endian, MSB first), so test inputs are
plain `List Bool` literals. `canonical.bitlist.make` is the identity
wrapper.

DO NOT MODIFY — infrastructure.
-/

-- ── canonical.bitlist.make (identity constructor) ─────────────────
-- @review human: `make` is the identity on List Bool; sanity checks.
#guard canonical.bitlist.make [true, false] == [true, false]
#guard canonical.bitlist.make [] == ([] : List Bool)
#guard canonical.bitlist.make [false, false, false, false] == [false, false, false, false]

-- ── canonical.bitlist.length ──────────────────────────────────────
-- @review human: no test cases in benchmark.json; sanity checks.
#guard canonical.bitlist.length [] == 0
#guard canonical.bitlist.length [true, false, true] == 3
#guard canonical.bitlist.length [true] == 1
#guard canonical.bitlist.length [false, false, false, false, false, false, false, false] == 8

-- ── canonical.bitlist.add (concatenation) ─────────────────────────
-- benchmark.json test: mk [T,T] + mk [T,F] = mk [T,T,T,F]
#guard canonical.bitlist.add [true, true] [true, false] == [true, true, true, false]
-- empty-left identity: [] ++ x = x
#guard canonical.bitlist.add [] [true, false, true] == [true, false, true]
-- empty-right identity: x ++ [] = x
#guard canonical.bitlist.add [true, false, true] [] == [true, false, true]
-- all-zeros concatenation
#guard canonical.bitlist.add [false, false] [false, false] == [false, false, false, false]

-- ── canonical.bitlist.bitlist_getitem (index) ─────────────────────
-- benchmark.json test: mk [T,T,T,T,F,T,T][2] = true (3rd bit from MSB of 1111011)
-- Use pattern match to avoid needing BEq on Except String (Sum Bool Bitlist).
#guard (match canonical.bitlist.bitlist_getitem [true, true, true, true, false, true, true]
           (Sum.inl (2 : Int)) with
  | Except.ok (Sum.inl b) => b == true
  | _ => false)

-- out-of-bounds positive index → error
#guard (match canonical.bitlist.bitlist_getitem [true, false] (Sum.inl (5 : Int)) with
  | Except.error _ => true
  | _ => false)

-- negative index: -1 returns the last bit (LSB) of [T,F,T] = T
#guard (match canonical.bitlist.bitlist_getitem [true, false, true] (Sum.inl (-1 : Int)) with
  | Except.ok (Sum.inl b) => b == true
  | _ => false)

-- slice: [T,T,T,T,F,T,T][0:3] = [T,T,T]
#guard (match canonical.bitlist.bitlist_getitem [true, true, true, true, false, true, true]
           (Sum.inr (some (0 : Int), some (3 : Int), none)) with
  | Except.ok (Sum.inr bl) => bl == [true, true, true]
  | _ => false)

-- ── canonical.bitlist.bitlistToInt (big-endian to Nat) ────────────
-- benchmark.json test: mk [T,T,T,T,F,T,T] = 1111011₂ = 123
#guard canonical.bitlist.bitlistToInt [true, true, true, true, false, true, true] == 123
-- empty bit vector → 0
#guard canonical.bitlist.bitlistToInt [] == 0
-- all-zeros → 0
#guard canonical.bitlist.bitlistToInt [false, false, false, false] == 0
-- all-ones (4 bits) → 1111₂ = 15
#guard canonical.bitlist.bitlistToInt [true, true, true, true] == 15
-- single one bit (MSB position 0 of 3-bit) = 100₂ = 4
#guard canonical.bitlist.bitlistToInt [true, false, false] == 4
