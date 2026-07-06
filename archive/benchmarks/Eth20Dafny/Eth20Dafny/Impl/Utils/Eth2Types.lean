import Eth20Dafny.Impl.UtilsEth2Types
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eth20Dafny.Impl.Utils.Eth2Types

Core type aliases for Eth2.0 serialization and fixed-width identifiers.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
-/


-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Eth20Dafny

abbrev byte := UInt8

structure BitlistWithLength where
  s : List Bool
  limit : Nat
  deriving Repr, DecidableEq

abbrev CorrectBitlist := BitlistWithLength

abbrev Version := Bytes4

abbrev ForkDigest := Bytes4

abbrev Domain := Bytes32

end Eth20Dafny
