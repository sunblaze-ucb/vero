/-!
# Json.Impl.Values

Foundation JSON value vocabulary translated from `JSON.Values`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

structure Decimal where
  n : Int
  e10 : Int
  deriving Repr, DecidableEq, BEq

inductive JSON where
  | null : JSON
  | bool (b : Bool) : JSON
  | string (str : String) : JSON
  | number (num : Decimal) : JSON
  | object (obj : List (String × JSON)) : JSON
  | array (arr : List JSON) : JSON
  deriving Repr

-- Spec helpers (no markers - fixed vocabulary)

def decimalOfInt (n : Int) : Decimal := { n := n, e10 := 0 }

end JSON
