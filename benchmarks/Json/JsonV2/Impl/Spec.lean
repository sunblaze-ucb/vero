import JsonV2.Impl.Errors

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Json.Impl.Spec

Serialization specification support translated from `JSON.Spec`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

abbrev bytes := List UInt8

abbrev result (T : Type) := SerializationResult T

-- API signatures (no markers - fixed vocabulary)

abbrev IntToBytesSig := Int → bytes

-- !benchmark @start global_aux
def decimalDigitByte (d : Nat) : UInt8 :=
  UInt8.ofNat (48 + d)

def natDecimalBytesAux : Nat → Nat → List UInt8
  | 0, n => [decimalDigitByte (n % 10)]
  | fuel + 1, n =>
      if n < 10 then
        [decimalDigitByte n]
      else
        natDecimalBytesAux fuel (n / 10) ++ [decimalDigitByte (n % 10)]

def intDecimalBytes (n : Int) : List UInt8 :=
  let body := natDecimalBytesAux n.natAbs n.natAbs
  if n < 0 then (45 : UInt8) :: body else body
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=intToBytes
-- !benchmark @end code_aux def=intToBytes

def intToBytes : IntToBytesSig :=
-- !benchmark @start code def=intToBytes
  intDecimalBytes
-- !benchmark @end code def=intToBytes

end JSON
