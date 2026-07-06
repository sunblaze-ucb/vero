import VerifiedIronkv.Impl.KeysT

/-!
# VerifiedIronkv.Impl.AbstractParametersT

Translated Verus vocabulary and reference implementations for `AbstractParametersT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

structure AbstractParameters where
  max_seqno : Nat
  max_delegations : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Bank


end Bank

