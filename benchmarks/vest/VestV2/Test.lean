import VestV2.Impl.Errors
import VestV2.Impl.Utils
import VestV2.Impl.RegularBytes
import VestV2.Impl.RegularEnd
import VestV2.Impl.RegularFail
import VestV2.Impl.RegularSuccess
import VestV2.Impl.RegularLeb128
import VestV2.Impl.RegularClone
import VestV2.Impl.RegularTag
import VestV2.Impl.BitcoinVarint

/-!
# VestV2.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations that live INSIDE the `code`
markers in `Impl/*.lean`. Before the LLM sees the benchmark, the
pipeline replaces marker contents with `sorry` — these guards catch
regressions in the reference impls themselves, not in LLM submissions.
The target here is the live bundle surface, not the entire frozen
support vocabulary imported by the project.

DO NOT MODIFY — infrastructure.
-/

-- BEq instance for Except (needed for #guard)
instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

-- BEq instance for U8 (needed for clone test)
deriving instance BEq for U8

-- ── RegularEnd ──────────────────────────────────────────────────
#guard VestV2.endParse [] == Except.ok (0, ())
#guard VestV2.endParse [0x00] == Except.error ParseError.NotEof
#guard VestV2.endSerialize () [] 0 == Except.ok 0

-- ── RegularFail ─────────────────────────────────────────────────
#guard (match VestV2.failParse [] with | .error _ => true | .ok _ => false)
#guard (match VestV2.failSerialize () [] 0 with | .error _ => true | .ok _ => false)

-- ── RegularSuccess ──────────────────────────────────────────────
#guard VestV2.successParse [0x01, 0x02] == Except.ok (0, ())
#guard VestV2.successSerialize () [] 0 == Except.ok 0

-- ── Utils ───────────────────────────────────────────────────────
#guard (VestV2.initVecU8 4).length == 4
#guard VestV2.initVecU8 3 == [0, 0, 0]
#guard VestV2.compareSlice [1, 2, 3] [1, 2, 3] == true
#guard VestV2.compareSlice [1, 2] [1, 2, 3] == false
#guard VestV2.compareSlice [1, 2, 3] [1, 2, 4] == false
#guard VestV2.setRange [0, 0, 0, 0] 1 [0xAA, 0xBB] == [0, 0xAA, 0xBB, 0]

-- ── Errors ──────────────────────────────────────────────────────
#guard VestV2.fromParseError ParseError.NotEof == Error.Parse ParseError.NotEof
#guard VestV2.fromSerializeError SerializeError.InsufficientBuffer == Error.Serialize SerializeError.InsufficientBuffer

-- ── RegularBytes ────────────────────────────────────────────────
#guard VestV2.variableParse { n := 2 } [1, 2, 3] == Except.ok (2, [1, 2])
#guard (match VestV2.variableParse { n := 5 } [1, 2, 3] with | .error _ => true | .ok _ => false)
#guard VestV2.variableSerialize { n := 2 } [1, 2] [0, 0, 0] 1 == Except.ok 2
#guard (match VestV2.variableSerialize { n := 2 } [1, 2] [0, 0, 0] 2 with | .error _ => true | .ok _ => false)
#guard VestV2.fixedParse { n := 2 } [1, 2, 3] == Except.ok (2, [1, 2])
#guard (match VestV2.fixedParse { n := 4 } [1, 2, 3] with | .error _ => true | .ok _ => false)
#guard VestV2.fixedSerialize { n := 2 } [1, 2] [0, 0, 0] 1 == Except.ok 2
#guard (match VestV2.fixedSerialize { n := 2 } [1, 2] [0, 0, 0] 2 with | .error _ => true | .ok _ => false)
#guard VestV2.tailParse [1, 2, 3] == Except.ok (3, [1, 2, 3])
#guard VestV2.tailSerialize [1, 2, 3] [0, 0, 0, 0] 1 == Except.ok 3
#guard (match VestV2.tailSerialize [1, 2, 3] [0, 0, 0, 0] 2 with | .error _ => true | .ok _ => false)

-- ── RegularLeb128 ───────────────────────────────────────────────
#guard VestV2.leb128Parse [0x7F] == Except.ok (1, 127)
#guard (match VestV2.leb128Parse [] with | .error _ => true | .ok _ => false)

-- ── BitcoinVarint ───────────────────────────────────────────────
#guard VestV2.btcVarintParse [0x42] == Except.ok (1, VarInt.U8 0x42)
#guard VestV2.btcVarintParse [0xFD, 0xFD, 0x00] == Except.ok (3, VarInt.U16 0x00FD)
#guard VestV2.btcVarintSerialize (VarInt.U8 0x42) [0] 0 == Except.ok 1
#guard VestV2.btcVarintSerialize (VarInt.U16 (UInt16.ofNat 0x00FD)) [0, 0, 0] 0 == Except.ok 3
#guard VestV2.btcVarintSerialize (VarInt.U32 (UInt32.ofNat 0x00010000)) [0, 0, 0, 0, 0] 0 == Except.ok 5
#guard VestV2.btcVarintSerialize (VarInt.U64 (UInt64.ofNat 0x0000000100000000)) [0, 0, 0, 0, 0, 0, 0, 0, 0] 0 == Except.ok 9
#guard (match VestV2.btcVarintSerialize (VarInt.U8 0x42) [] 0 with | .error _ => true | .ok _ => false)
#guard (match VestV2.btcVarintSerialize (VarInt.U16 (UInt16.ofNat 0x00FD)) [0, 0] 0 with | .error _ => true | .ok _ => false)
#guard (match VestV2.btcVarintSerialize (VarInt.U32 (UInt32.ofNat 0x00010000)) [0, 0, 0, 0] 0 with | .error _ => true | .ok _ => false)
#guard (match VestV2.btcVarintSerialize (VarInt.U64 (UInt64.ofNat 0x0000000100000000)) [0, 0, 0, 0, 0, 0, 0, 0] 0 with | .error _ => true | .ok _ => false)

-- ── RegularClone ────────────────────────────────────────────────
#guard VestV2.cloneU8 U8.mk == U8.mk
#guard (match VestV2.cloneU16Le U16Le.mk with | U16Le.mk => true)
#guard (match VestV2.cloneU32Le U32Le.mk with | U32Le.mk => true)
#guard (match VestV2.cloneU64Le U64Le.mk with | U64Le.mk => true)
#guard (match VestV2.cloneTail Tail.mk with | Tail.mk => true)
#guard (VestV2.cloneVariable { n := 3 }).n == 3
#guard (VestV2.cloneFixed { n := 2 }).n == 2

-- ── RegularTag ──────────────────────────────────────────────────
#guard VestV2.tagParse 0x42 [0x42, 0x00] == Except.ok (1, ())
#guard (match VestV2.tagParse 0x42 [0x43, 0x00] with | .error _ => true | .ok _ => false)
#guard VestV2.tagSerialize 0x42 () [0] 0 == Except.ok 1
#guard (match VestV2.tagSerialize 0x42 () [] 0 with | .error _ => true | .ok _ => false)
