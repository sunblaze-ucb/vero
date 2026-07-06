import BitManipulation.Bundle

/-!
# BitManipulation.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring.

DO NOT MODIFY — this is benchmark infrastructure.
-/

structure RepoImpl where
  bitManipulation : BitManipulationBundle

def canonical : RepoImpl where
  bitManipulation := {
    binary_and := BitManipulation.binary_and
    binary_or := BitManipulation.binary_or
    logical_left_shift := BitManipulation.logical_left_shift
    logical_right_shift := BitManipulation.logical_right_shift
    arithmetic_right_shift := BitManipulation.arithmetic_right_shift
    twos_complement := BitManipulation.twos_complement
    binary_xor := BitManipulation.binary_xor
    set_bit := BitManipulation.set_bit
    clear_bit := BitManipulation.clear_bit
    flip_bit := BitManipulation.flip_bit
    is_bit_set := BitManipulation.is_bit_set
    get_bit := BitManipulation.get_bit
  }
