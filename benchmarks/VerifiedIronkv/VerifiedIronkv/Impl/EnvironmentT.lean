import VerifiedIronkv.Impl.ArgsT

/-!
# VerifiedIronkv.Impl.EnvironmentT

Translated Verus vocabulary and reference implementations for `EnvironmentT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

structure LPacket (IdType : Type) (MessageType : Type) where
  dst : IdType
  src : IdType
  msg : MessageType
  deriving Repr, DecidableEq, BEq, Inhabited

inductive LIoOp (IdType MessageType : Type) where
  | Send (s : LPacket IdType MessageType)
  | Receive (r : LPacket IdType MessageType)
  | TimeoutReceive
  | ReadClock (t : Int)
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Bank


end Bank

