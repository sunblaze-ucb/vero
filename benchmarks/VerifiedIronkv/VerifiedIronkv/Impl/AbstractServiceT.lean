import VerifiedIronkv.Impl.MessageT

/-!
# VerifiedIronkv.Impl.AbstractServiceT

Translated Verus vocabulary and reference implementations for `AbstractServiceT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

inductive AppRequest where
  | AppGetRequest (seqno : Nat) (key : AbstractKey)
  | AppSetRequest (seqno : Nat) (key : AbstractKey) (ov : Option AbstractValue)
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Bank


end Bank

