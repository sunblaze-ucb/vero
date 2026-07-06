import VerifiedIronkv.Impl.NetworkT

/-!
# VerifiedIronkv.Impl.SingleDeliveryT

Translated Verus vocabulary and reference implementations for `SingleDeliveryT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

abbrev TombstoneTable := List (AbstractEndPoint × Nat)

abbrev AckList (MT : Type) := List (SingleMessage MT)

structure AckState (MT : Type) where
  num_packets_acked : Nat
  un_acked : AckList MT
  deriving Repr, DecidableEq, BEq, Inhabited

abbrev SendState (MT : Type) := List (AbstractEndPoint × AckState MT)

structure SingleDelivery (MT : Type) where
  receive_state : TombstoneTable
  send_state : SendState MT
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Bank


end Bank

