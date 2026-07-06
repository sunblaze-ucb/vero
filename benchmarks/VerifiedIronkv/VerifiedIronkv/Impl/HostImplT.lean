import VerifiedIronkv.Impl.HostImplV

/-!
# VerifiedIronkv.Impl.HostImplT

Translated Verus vocabulary and reference implementations for `HostImplT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

abbrev Ios := List NetEvent

structure EventResults where
  recvs : List NetEvent
  clocks : List NetEvent
  sends : List NetEvent
  ios : Ios
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Bank


end Bank

