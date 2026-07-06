import VerifiedIronkv.Impl.MarshalV

/-!
# VerifiedIronkv.Impl.MarshalIronshtSpecificV

Translated Verus vocabulary and reference implementations for `MarshalIronshtSpecificV`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

def view_equal {A : Type} [DecidableEq A] (x y : A) : Bool :=
  decide (x = y)

def is_marshalable : CSingleMessage → Bool
  | CSingleMessage.Message _ dst _ => decide (dst.id.length < 1048576)
  | CSingleMessage.Ack _ => true
  | CSingleMessage.InvalidMessage => false

namespace Bank


end Bank

