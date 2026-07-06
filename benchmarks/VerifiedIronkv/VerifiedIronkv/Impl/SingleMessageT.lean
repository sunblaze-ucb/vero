import VerifiedIronkv.Impl.AbstractServiceT

/-!
# VerifiedIronkv.Impl.SingleMessageT

Translated Verus vocabulary and reference implementations for `SingleMessageT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

inductive SingleMessage (MT : Type) where
  | Message (seqno : Nat) (dst : AbstractEndPoint) (m : MT)
  | Ack (ack_seqno : Nat)
  | InvalidMessage
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Bank


end Bank

