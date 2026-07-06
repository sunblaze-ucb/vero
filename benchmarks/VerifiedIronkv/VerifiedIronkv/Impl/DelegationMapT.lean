import VerifiedIronkv.Impl.EndpointHashmapT

/-!
# VerifiedIronkv.Impl.DelegationMapT

Translated Verus vocabulary and reference implementations for `DelegationMapT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

structure AbstractDelegationMap where
  value : List (AbstractKey × AbstractEndPoint)
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Bank


end Bank

