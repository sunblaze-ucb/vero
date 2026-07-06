import VerifiedIronkv.Impl.DelegationMapV

/-!
# VerifiedIronkv.Impl.MessageT

Translated Verus vocabulary and reference implementations for `MessageT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

inductive Message where
  | GetRequest (key : AbstractKey)
  | SetRequest (key : AbstractKey) (value : Option AbstractValue)
  | Reply (key : AbstractKey) (value : Option AbstractValue)
  | Redirect (key : AbstractKey) (id : AbstractEndPoint)
  | Shard (range : KeyRange AbstractKey) (recipient : AbstractEndPoint)
  | Delegate (range : KeyRange AbstractKey) (h : Hashtable)
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Bank


end Bank

