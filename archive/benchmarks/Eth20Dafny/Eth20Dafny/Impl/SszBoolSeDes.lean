-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eth20Dafny.Impl.SszBoolSeDes

Boolean serialization/deserialization helpers translated from
`ssz/BoolSeDes.dfy`.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Eth20Dafny

-- ── API signatures (no markers — fixed vocabulary) ────

abbrev BoolToBytesSig := Bool → List UInt8

abbrev BoolSeDesByteToBoolSig := List UInt8 → Bool

end Eth20Dafny

-- !benchmark @start code_aux def=boolToBytes
-- !benchmark @end code_aux def=boolToBytes

def Eth20Dafny.boolToBytes : Eth20Dafny.BoolToBytesSig :=
-- !benchmark @start code def=boolToBytes
  fun b => [if b then UInt8.ofNat 1 else UInt8.ofNat 0]
-- !benchmark @end code def=boolToBytes

-- !benchmark @start code_aux def=boolSeDesByteToBool
-- !benchmark @end code_aux def=boolSeDesByteToBool

def Eth20Dafny.boolSeDesByteToBool : Eth20Dafny.BoolSeDesByteToBoolSig :=
-- !benchmark @start code def=boolSeDesByteToBool
  fun xb =>
    match xb with
    | x :: _ => x.toNat > 0
    | [] => false
-- !benchmark @end code def=boolSeDesByteToBool
