import BitManipulation.Impl.BinaryAndOperator
import BitManipulation.Impl.BinaryOrOperator
import BitManipulation.Impl.BinaryShifts
import BitManipulation.Impl.BinaryTwosComplement
import BitManipulation.Impl.BinaryXorOperator
import BitManipulation.Impl.SingleBitManipulationOperations

/-!
# BitManipulation.Bundle

Per-package implementation bundle. Collects all API signatures into
one `structure BitManipulationBundle`.

DO NOT MODIFY — benchmark infrastructure.
-/

structure BitManipulationBundle where
  binary_and : BitManipulation.BinaryAndSig
  binary_or : BitManipulation.BinaryOrSig
  logical_left_shift : BitManipulation.LogicalLeftShiftSig
  logical_right_shift : BitManipulation.LogicalRightShiftSig
  arithmetic_right_shift : BitManipulation.ArithmeticRightShiftSig
  twos_complement : BitManipulation.TwosComplementSig
  binary_xor : BitManipulation.BinaryXorSig
  set_bit : BitManipulation.SetBitSig
  clear_bit : BitManipulation.ClearBitSig
  flip_bit : BitManipulation.FlipBitSig
  is_bit_set : BitManipulation.IsBitSetSig
  get_bit : BitManipulation.GetBitSig
