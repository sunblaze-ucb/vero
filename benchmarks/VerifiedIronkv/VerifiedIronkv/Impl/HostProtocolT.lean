import VerifiedIronkv.Impl.NetShtV

/-!
# VerifiedIronkv.Impl.HostProtocolT

Translated Verus vocabulary and reference implementations for `HostProtocolT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

inductive Step where
  | ReceivePacket
  | ProcessReceivedPacket
  | SpontaneouslyRetransmit
  | Stutter
  | IgnoreUnparseablePacket
  | IgnoreNonsensicalDelegationPacket
  deriving Repr, DecidableEq, BEq, Inhabited

abbrev LSHTIo := LIoOp AbstractEndPoint (SingleMessage Message)

abbrev AbstractIos := List LSHTIo

structure AbstractConstants where
  root_identity : AbstractEndPoint
  host_ids : List AbstractEndPoint
  params : AbstractParameters
  me : AbstractEndPoint
  deriving Repr, DecidableEq, BEq, Inhabited

structure AbstractHostState where
  constants : AbstractConstants
  delegation_map : AbstractDelegationMap
  h : Hashtable
  sd : SingleDelivery Message
  received_packet : Option Packet
  num_delegations : Int
  received_requests : List AppRequest
  deriving Repr, DecidableEq, BEq, Inhabited

def okay_to_ignore_packets : Bool :=
  true

namespace Bank


end Bank

