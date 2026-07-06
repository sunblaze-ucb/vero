import VerifiedIronkv.Impl.MainT

/-!
# VerifiedIronkv.Impl.HashmapT

Translated Verus vocabulary and reference implementations for `HashmapT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

structure CKeyHashMap where
  m : List (CKey × List Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

structure CKeyKV where
  k : CKey
  v : List Nat
  deriving Repr, DecidableEq, BEq, Inhabited

def hashmapTView (x : CKeyKV) : AbstractKey × List Nat :=
  (x.k, x.v)

namespace Bank


end Bank

