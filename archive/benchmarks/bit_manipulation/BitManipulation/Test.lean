import BitManipulation.Impl.BinaryAndOperator
import BitManipulation.Impl.BinaryOrOperator
import BitManipulation.Impl.BinaryShifts
import BitManipulation.Impl.BinaryTwosComplement
import BitManipulation.Impl.BinaryXorOperator
import BitManipulation.Impl.SingleBitManipulationOperations
import BitManipulation.Harness

/-!
# BitManipulation.Test

Executable conformance tests. `#guard` assertions run against the
`canonical` wiring. Before the LLM sees the benchmark, the pipeline
replaces `sorry` stubs — the inventory below activates post-fill.

DO NOT MODIFY — infrastructure.
-/

-- Sentinel — proves Test.lean is wired and counts toward the validator's
-- guard tally. Real test cases live in the curator block below.
#guard True

-- ── BinaryAndOperator ─────────────────────────
#guard canonical.bitManipulation.binary_and 25 32 = "0b000000"
#guard canonical.bitManipulation.binary_and 37 50 = "0b100000"
#guard canonical.bitManipulation.binary_and 21 30 = "0b10100"
#guard canonical.bitManipulation.binary_and 58 73 = "0b0001000"
#guard canonical.bitManipulation.binary_and 0 255 = "0b00000000"
#guard canonical.bitManipulation.binary_and 256 256 = "0b100000000"
#guard canonical.bitManipulation.binary_and ((2: Int) ^ (31: Nat) - 1) ((2: Int) ^ (31: Nat) - 1) = "0b1111111111111111111111111111111"

-- ── BinaryOrOperator ─────────────────────────
#guard canonical.bitManipulation.binary_or 25 32 = "0b111001"
#guard canonical.bitManipulation.binary_or 37 50 = "0b110111"
#guard canonical.bitManipulation.binary_or 21 30 = "0b11111"
#guard canonical.bitManipulation.binary_or 58 73 = "0b1111011"
#guard canonical.bitManipulation.binary_or 0 255 = "0b11111111"
#guard canonical.bitManipulation.binary_or 0 256 = "0b100000000"
#guard canonical.bitManipulation.binary_or 0 0 = "0b0"
#guard canonical.bitManipulation.binary_or ((2 : Int) ^ (100 : Nat)) ((2 : Int) ^ (100 : Nat)) = "0b1" ++ String.mk (List.replicate 100 '0')

-- ── BinaryShifts ─────────────────────────
#guard canonical.bitManipulation.logical_left_shift 0 1 = "0b00"
#guard canonical.bitManipulation.logical_left_shift 1 1 = "0b10"
#guard canonical.bitManipulation.logical_left_shift 1 5 = "0b100000"
#guard canonical.bitManipulation.logical_left_shift 17 2 = "0b1000100"
#guard canonical.bitManipulation.logical_left_shift 1983 4 = "0b111101111110000"
#guard canonical.bitManipulation.logical_right_shift 0 1 = "0b0"
#guard canonical.bitManipulation.logical_right_shift 1 1 = "0b0"
#guard canonical.bitManipulation.logical_right_shift 1 5 = "0b0"
#guard canonical.bitManipulation.logical_right_shift 17 2 = "0b100"
#guard canonical.bitManipulation.logical_right_shift 1983 4 = "0b1111011"
#guard canonical.bitManipulation.arithmetic_right_shift 0 1 = "0b00"
#guard canonical.bitManipulation.arithmetic_right_shift 1 1 = "0b00"
#guard canonical.bitManipulation.arithmetic_right_shift (-1) 1 = "0b11"
#guard canonical.bitManipulation.arithmetic_right_shift 17 2 = "0b000100"
#guard canonical.bitManipulation.arithmetic_right_shift (-17) 2 = "0b111011"
#guard canonical.bitManipulation.arithmetic_right_shift (-1983) 4 = "0b111110000100"

-- ── BinaryTwosComplement ─────────────────────────
#guard canonical.bitManipulation.twos_complement (-1) = "0b11"
#guard canonical.bitManipulation.twos_complement (-5) = "0b1011"
#guard canonical.bitManipulation.twos_complement (-17) = "0b101111"
#guard canonical.bitManipulation.twos_complement (-207) = "0b100110001"
#guard canonical.bitManipulation.twos_complement 0 = "0b0"
#guard canonical.bitManipulation.twos_complement (-((2 : Int) ^ (31 : Nat))) = "0b110000000000000000000000000000000"

-- ── BinaryXorOperator ─────────────────────────
#guard canonical.bitManipulation.binary_xor 25 32 = "0b111001"
#guard canonical.bitManipulation.binary_xor 37 50 = "0b010111"
#guard canonical.bitManipulation.binary_xor 21 30 = "0b01011"
#guard canonical.bitManipulation.binary_xor 58 73 = "0b1110011"
#guard canonical.bitManipulation.binary_xor 0 255 = "0b11111111"
#guard canonical.bitManipulation.binary_xor 256 256 = "0b000000000"
#guard canonical.bitManipulation.binary_xor 0 0 = "0b0"
#guard canonical.bitManipulation.binary_xor 1 0 = "0b1"
#guard canonical.bitManipulation.binary_xor 0 1 = "0b1"
#guard canonical.bitManipulation.binary_xor ((2 : Int) ^ (100 : Nat)) ((2 : Int) ^ (100 : Nat)) = "0b" ++ String.mk (List.replicate 100 '0') ++ "0"
#guard canonical.bitManipulation.binary_xor ((2 : Int) ^ (100 : Nat)) 0 = "0b1" ++ String.mk (List.replicate 100 '0')

-- ── SingleBitManipulationOperations ─────────────────────────
#guard canonical.bitManipulation.set_bit 13 1 = 15
#guard canonical.bitManipulation.set_bit 0 5 = 32
#guard canonical.bitManipulation.set_bit 15 1 = 15
#guard canonical.bitManipulation.set_bit 0 0 = 1
#guard canonical.bitManipulation.clear_bit 18 1 = 16
#guard canonical.bitManipulation.clear_bit 0 5 = 0
#guard canonical.bitManipulation.clear_bit 15 3 = 7
#guard canonical.bitManipulation.clear_bit 1 0 = 0
#guard canonical.bitManipulation.flip_bit 5 1 = 7
#guard canonical.bitManipulation.flip_bit 5 0 = 4
#guard canonical.bitManipulation.flip_bit 0 2 = 4
#guard canonical.bitManipulation.flip_bit 15 3 = 7
#guard canonical.bitManipulation.is_bit_set 10 0 = false
#guard canonical.bitManipulation.is_bit_set 10 1 = true
#guard canonical.bitManipulation.is_bit_set 10 2 = false
#guard canonical.bitManipulation.is_bit_set 10 3 = true
#guard canonical.bitManipulation.is_bit_set 0 17 = false
#guard canonical.bitManipulation.get_bit 10 0 = 0
#guard canonical.bitManipulation.get_bit 10 1 = 1
#guard canonical.bitManipulation.get_bit 10 2 = 0
#guard canonical.bitManipulation.get_bit 10 3 = 1
#guard canonical.bitManipulation.get_bit 0 17 = 0
