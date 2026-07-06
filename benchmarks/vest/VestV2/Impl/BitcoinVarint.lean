import VestV2.Impl.Errors
import VestV2.Impl.Properties

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VestV2.Impl.BitcoinVarint

Bitcoin variable-length integer combinator. Parses and serializes
compact-size integers per the Bitcoin protocol specification.
Values < 0xFD encode as a single byte; 0xFD tag → 2 LE bytes (U16);
0xFE tag → 4 LE bytes (U32); 0xFF tag → 8 LE bytes (U64).

Types and signatures are fixed vocabulary (DO NOT MODIFY).
Implement only the function bodies.
-/

-- ── Types (no markers — fixed vocabulary) ─────────────

/-- Combinator for parsing and serializing Bitcoin variable-length integers. -/
structure BtcVarint

/-- Enum representing a Bitcoin variable-length integer. -/
inductive VarInt where
  | U8 (_ : UInt8) : VarInt
  | U16 (_ : UInt16) : VarInt
  | U32 (_ : UInt32) : VarInt
  | U64 (_ : UInt64) : VarInt
  deriving Repr, DecidableEq, BEq

/-- Predicate for checking if a u16 is ≥ 0xFD. -/
structure PredU16LeFit

/-- Predicate for checking if a u32 is ≥ 0x10000. -/
structure PredU32LeFit

/-- Predicate for checking if a u64 is ≥ 0x100000000. -/
structure PredU64LeFit

/-- Mapper for converting between Bitcoin VarInts and internal representations. -/
structure VarIntMapper

/-- Continuation for parsing and serializing Bitcoin variable-length integers. -/
structure BtVarintCont

-- ── Spec helpers (no markers — vocabulary) ─────────────

/-- Apply the u16 fit predicate: value ≥ 0xFD. -/
def predU16LeFitApply (v : UInt16) : Bool :=
  decide (v.toNat ≥ 0xFD)

/-- Apply the u32 fit predicate: value ≥ 0x10000. -/
def predU32LeFitApply (v : UInt32) : Bool :=
  decide (v.toNat ≥ 0x10000)

/-- Apply the u64 fit predicate: value ≥ 0x100000000. -/
def predU64LeFitApply (v : UInt64) : Bool :=
  decide (v.toNat ≥ 0x100000000)

/-- Spec-level parse for Bitcoin VarInt. Follows the Bitcoin protocol:
    tag byte ≤ 0xFC → U8, 0xFD → U16 LE, 0xFE → U32 LE, 0xFF → U64 LE. -/
def VarInt.spec_parse (s : List UInt8) : Option (Int × VarInt) :=
  match s with
  | [] => none
  | b :: rest =>
    if b.toNat ≤ 0xFC then
      some (1, VarInt.U8 b)
    else if b.toNat == 0xFD then
      match rest with
      | b0 :: b1 :: _ =>
        let val := UInt16.ofNat (b0.toNat + b1.toNat * 256)
        if predU16LeFitApply val then some (3, VarInt.U16 val)
        else none
      | _ => none
    else if b.toNat == 0xFE then
      match rest with
      | b0 :: b1 :: b2 :: b3 :: _ =>
        let val := UInt32.ofNat (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216)
        if predU32LeFitApply val then some (5, VarInt.U32 val)
        else none
      | _ => none
    else -- 0xFF
      match rest with
      | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: _ =>
        let val := UInt64.ofNat (b0.toNat + b1.toNat * 256 + b2.toNat * 65536
          + b3.toNat * 16777216 + b4.toNat * 4294967296 + b5.toNat * 1099511627776
          + b6.toNat * 281474976710656 + b7.toNat * 72057594037927936)
        if predU64LeFitApply val then some (9, VarInt.U64 val)
        else none
      | _ => none

namespace VestV2

-- ── API signatures (no markers — fixed vocabulary) ────

/-- Parse a Bitcoin compact-size integer from a byte slice;
    returns (bytes_consumed, VarInt). -/
abbrev BtcVarintParseSig := List UInt8 → Except ParseError (Nat × VarInt)

/-- Serialize a Bitcoin compact-size integer into buf at pos;
    returns the number of bytes written (1, 3, 5, or 9). -/
abbrev BtcVarintSerializeSig := VarInt → List UInt8 → Nat → Except SerializeError Nat

end VestV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ────────────────────

-- !benchmark @start code_aux def=btcVarintParse
-- !benchmark @end code_aux def=btcVarintParse

def VestV2.btcVarintParse : VestV2.BtcVarintParseSig :=
-- !benchmark @start code def=btcVarintParse
  fun s =>
    match s with
    | [] => Except.error ParseError.UnexpectedEndOfInput
    | b :: rest =>
      if b.toNat ≤ 0xFC then
        Except.ok (1, VarInt.U8 b)
      else if b.toNat == 0xFD then
        match rest with
        | b0 :: b1 :: _ =>
          let val := UInt16.ofNat (b0.toNat + b1.toNat * 256)
          if predU16LeFitApply val then Except.ok (3, VarInt.U16 val)
          else Except.error ParseError.RefinedPredicateFailed
        | _ => Except.error ParseError.UnexpectedEndOfInput
      else if b.toNat == 0xFE then
        match rest with
        | b0 :: b1 :: b2 :: b3 :: _ =>
          let val := UInt32.ofNat (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216)
          if predU32LeFitApply val then Except.ok (5, VarInt.U32 val)
          else Except.error ParseError.RefinedPredicateFailed
        | _ => Except.error ParseError.UnexpectedEndOfInput
      else -- 0xFF
        match rest with
        | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: _ =>
          let val := UInt64.ofNat (b0.toNat + b1.toNat * 256 + b2.toNat * 65536
            + b3.toNat * 16777216 + b4.toNat * 4294967296 + b5.toNat * 1099511627776
            + b6.toNat * 281474976710656 + b7.toNat * 72057594037927936)
          if predU64LeFitApply val then Except.ok (9, VarInt.U64 val)
          else Except.error ParseError.RefinedPredicateFailed
        | _ => Except.error ParseError.UnexpectedEndOfInput
-- !benchmark @end code def=btcVarintParse

-- !benchmark @start code_aux def=btcVarintSerialize
-- !benchmark @end code_aux def=btcVarintSerialize

def VestV2.btcVarintSerialize : VestV2.BtcVarintSerializeSig :=
-- !benchmark @start code def=btcVarintSerialize
  fun v buf pos =>
    match v with
    | VarInt.U8 _ =>
      if pos + 1 ≤ buf.length then Except.ok 1
      else Except.error SerializeError.InsufficientBuffer
    | VarInt.U16 _ =>
      if pos + 3 ≤ buf.length then Except.ok 3
      else Except.error SerializeError.InsufficientBuffer
    | VarInt.U32 _ =>
      if pos + 5 ≤ buf.length then Except.ok 5
      else Except.error SerializeError.InsufficientBuffer
    | VarInt.U64 _ =>
      if pos + 9 ≤ buf.length then Except.ok 9
      else Except.error SerializeError.InsufficientBuffer
-- !benchmark @end code def=btcVarintSerialize
