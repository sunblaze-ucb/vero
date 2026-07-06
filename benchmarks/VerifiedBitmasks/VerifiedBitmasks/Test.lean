import VerifiedBitmasks.Impl.BitFields
import VerifiedBitmasks.Impl.MachineWords
import VerifiedBitmasks.Impl.BitmaskSpec
import VerifiedBitmasks.Impl.BitmaskIF

/-!
# VerifiedBitmasks.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations that live INSIDE the `code` markers
in `Impl/*.lean`. Before the LLM sees the benchmark, the pipeline
replaces marker contents with `sorry` — these guards catch regressions
in the reference impls themselves, not in LLM submissions.

DO NOT MODIFY — infrastructure.
-/

open VerifiedBitmasks

-- ── MachineWords tests ─────────────────────────────────────────────────

-- bitwiseOnes is the all-ones UInt64 constant (0xffff_ffff_ffff_ffff).
#guard bitwiseOnes == 0xffff_ffff_ffff_ffff

-- bitwiseZeros is the zero UInt64 constant.
#guard bitwiseZeros == 0

-- bitwiseBit 0 equals 1 (only the least-significant bit set).
#guard bitwiseBit 0 == 1

-- bitwiseBit 3 equals 8 (only bit 3 set: 2^3 = 8).
#guard bitwiseBit 3 == 8

-- 0b1010 AND 0b1100 = 0b1000 (10 AND 12 = 8).
#guard bitwiseAnd 0b1010 0b1100 == 0b1000

-- 0b1010 OR 0b1100 = 0b1110 (10 OR 12 = 14).
#guard bitwiseOr 0b1010 0b1100 == 0b1110

-- XOR of any value with itself is zero.
#guard bitwiseXor 42 42 == 0

-- ── BitmaskSpec tests ──────────────────────────────────────────────────

-- A new all-zeros bitmask of 8 bits has 8 bits.
#guard bitmask_nbits (bitmask_new_zeros 8) == 8

-- Population count of a 4-bit all-ones bitmask is 4.
#guard bitmask_popcnt (bitmask_new_ones 4) == 4

-- After setting bit 3 in an 8-bit all-zeros bitmask, bit 3 reads back as true.
#guard bitmask_get_bit (bitmask_set_bit (bitmask_new_zeros 8) 3) 3 == true

-- ── BitmaskIF tests ────────────────────────────────────────────────────

-- bIF_newZeros 64 creates a bitmask with 64 bits.
#guard (VerifiedBitmasks.bIF_nbits (VerifiedBitmasks.bIF_newZeros 64)) == 64

-- bIF_newOnes 4 creates an all-ones bitmask.
#guard bIF_isOnes (VerifiedBitmasks.bIF_newOnes 4) == true
