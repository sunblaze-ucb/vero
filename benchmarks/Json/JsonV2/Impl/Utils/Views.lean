-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Json.Impl.Utils.Views

Byte-view vocabulary and reference implementation translated from
`JSON.Utils.Views.Core`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

structure View_ where
  s : List UInt8
  beg : UInt32
  end_ : UInt32
  deriving Repr, DecidableEq, BEq

abbrev View := View_

-- Spec helpers (no markers - fixed vocabulary)

def view__Empty : View_ := { s := [], beg := 0, end_ := 0 }

def view__Valid? (v : View_) : Bool :=
  decide
    (v.beg.toNat ≤ v.end_.toNat ∧
     v.end_.toNat ≤ v.s.length ∧
     v.s.length < UInt32.size)

def view__Length (v : View_) : UInt32 := v.end_ - v.beg

def view__Bytes (v : View_) : List UInt8 :=
  v.s.drop v.beg.toNat |>.take ((v.end_ - v.beg).toNat)

def view__OfBytes (bs : List UInt8) : View_ :=
  { s := bs, beg := 0, end_ := UInt32.ofNat bs.length }

-- API signatures (no markers - fixed vocabulary)

abbrev View_CopyToSig := View_ → List UInt8 → UInt32 → List UInt8

end JSON

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=view__CopyTo
-- !benchmark @end code_aux def=view__CopyTo

def JSON.view__CopyTo : JSON.View_CopyToSig :=
-- !benchmark @start code def=view__CopyTo
  fun v dest start =>
    dest.take start.toNat ++
      JSON.view__Bytes v ++
      dest.drop (start.toNat + (JSON.view__Length v).toNat)
-- !benchmark @end code def=view__CopyTo
