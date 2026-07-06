import VerifiedIronkv.Impl.CmessageV

/-!
# VerifiedIronkv.Impl.NetworkT

Translated Verus vocabulary and reference implementations for `NetworkT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

abbrev PMsg := SingleMessage Message

structure Packet where
  dst : AbstractEndPoint
  src : AbstractEndPoint
  msg : PMsg
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Bank


end Bank

