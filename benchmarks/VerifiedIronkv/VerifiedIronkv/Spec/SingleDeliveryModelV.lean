import VerifiedIronkv.Harness

/-!
# VerifiedIronkv.Spec.SingleDeliveryModelV

Frozen specifications for `SingleDeliveryModelV`.

DO NOT MODIFY — curator-given content.
-/

/-- `new_impl` returns the source ghost lookup freshness branch for represented receive-state maps; the abstract `SingleDelivery.new_single_message` bridge remains separate vocabulary. -/
def spec_new_impl_matches_new_single_message (impl : RepoImpl) : Prop :=
  ∀ (self : CSingleDelivery) (pkt : CPacket)
      (ghostLookup : AbstractEndPoint → Option Nat),
    valid_L337 self = true →
    cPacketAbstractableModel pkt = true →
    endpointHashmapEntriesRepresentMap self.receive_state.epmap.entries ghostLookup →
    impl.verifiedIronkv.new_impl self pkt =
      match pkt.msg with
      | CSingleMessage.Message seqno _ _ =>
          generatedU64Valid seqno &&
          decide (seqno > 0) &&
            decide (seqno - 1 = (ghostLookup (ioTView pkt.src)).getD 0)
      | _ => false

/-- Under a represented send-state map, `receive_ack_impl` follows the concrete source-body truncate/update branch; the abstract receive-ack relation remains separate vocabulary. -/
def spec_receive_ack_impl_matches_receive_ack (impl : RepoImpl) : Prop :=
  ∀ (self : CSingleDelivery) (pkt : CPacket) (ackSeqno : Nat)
      (ghostLookup : AbstractEndPoint → Option CAckState),
    valid_L337 self = true →
    cPacketAbstractableModel pkt = true →
    view_L218 pkt.msg = SingleMessage.Ack ackSeqno →
    endpointHashmapEntriesRepresentMap self.send_state.epmap.entries ghostLookup →
    let post := impl.verifiedIronkv.receive_ack_impl self pkt
    let oldAck := (ghostLookup (ioTView pkt.src)).getD defaultCAckState
    let newAck := truncateAckStateModel oldAck ackSeqno
    valid_L337 post = true ∧
      if generatedU64Valid ackSeqno then
        if ackSeqno > oldAck.num_packets_acked then
          post.receive_state = self.receive_state ∧
          post.send_state.epmap.entries =
            endpointEntriesSet self.send_state.epmap.entries (ioTView pkt.src) newAck
        else
          post = self
      else
        post = self

/-- Under a represented receive-state map, `receive_real_packet_impl` follows the concrete source-body freshness/update branch; the abstract receive-real relation remains separate vocabulary. -/
def spec_receive_real_packet_impl_matches_receive_real_packet (impl : RepoImpl) : Prop :=
  ∀ (self : CSingleDelivery) (pkt : CPacket) (seqno : Nat) (dst : AbstractEndPoint) (msg : Message)
      (ghostLookup : AbstractEndPoint → Option Nat),
    valid_L337 self = true →
    cPacketAbstractableModel pkt = true →
    view_L218 pkt.msg = SingleMessage.Message seqno dst msg →
    endpointHashmapEntriesRepresentMap self.receive_state.epmap.entries ghostLookup →
    let out := impl.verifiedIronkv.receive_real_packet_impl self pkt
    let lastSeqno := (ghostLookup (ioTView pkt.src)).getD 0
    let fresh := generatedU64Valid seqno && decide (seqno > 0) && decide (seqno - 1 = lastSeqno)
    valid_L337 out.1 = true ∧
      out.2 = fresh ∧
      if fresh then
        out.1.send_state = self.send_state ∧
        out.1.receive_state.epmap.entries =
          endpointEntriesSet self.receive_state.epmap.entries (ioTView pkt.src) (lastSeqno + 1)
      else
        out.1 = self

/-- `should_ack_sigle_message_impl` returns the source ghost lookup model for represented receive-state maps; the Lean API preserves the source typo. -/
def spec_should_ack_single_message_impl_matches_model (impl : RepoImpl) : Prop :=
  ∀ (self : CSingleDelivery) (pkt : CPacket)
      (ghostLookup : AbstractEndPoint → Option Nat),
    endpointHashmapEntriesRepresentMap self.receive_state.epmap.entries ghostLookup →
    impl.verifiedIronkv.should_ack_sigle_message_impl self pkt =
      match pkt.msg with
      | CSingleMessage.Message seqno _ _ =>
          generatedU64Valid seqno &&
          decide (seqno ≤ (ghostLookup (ioTView pkt.src)).getD 0)
      | _ => false

/-- Under a represented receive-state map, `maybe_ack_packet_impl` follows the concrete source-body Ack/None branch and any returned acknowledgement is valid for the packet. -/
def spec_maybe_ack_packet_impl_matches_model (impl : RepoImpl) : Prop :=
  ∀ (self : CSingleDelivery) (pkt : CPacket) (seqno : Nat) (dst : AbstractEndPoint) (msg : Message)
      (ghostLookup : AbstractEndPoint → Option Nat),
    valid_L337 self = true →
    cPacketAbstractableModel pkt = true →
    view_L218 pkt.msg = SingleMessage.Message seqno dst msg →
    endpointHashmapEntriesRepresentMap self.receive_state.epmap.entries ghostLookup →
    let ack := impl.verifiedIronkv.maybe_ack_packet_impl self pkt
    let shouldAck := generatedU64Valid seqno && decide (seqno ≤ (ghostLookup (ioTView pkt.src)).getD 0)
    (if shouldAck then
      ack = some { dst := pkt.src, src := pkt.dst, msg := CSingleMessage.Ack seqno }
    else
      ack = none) ∧
    (∀ a, ack = some a → validAckPacket a pkt)

/-- `receive_impl` preserves validity, returns valid acknowledgement payloads when present, and preserves the source freshness polarity of receive results. -/
def spec_receive_impl_matches_receive (impl : RepoImpl) : Prop :=
  ∀ (self : CSingleDelivery) (pkt : CPacket), valid_L337 self = true → cPacketAbstractableModel pkt = true → let out := impl.verifiedIronkv.receive_impl self pkt; valid_L337 out.1 = true ∧ receiveImplResultModel self out pkt ∧ (∀ ack, receiveImplResultAck out.2 = some ack → validAckPacket ack pkt) ∧ receiveImplResultAbstractedAckSetSemantics out.2

/-- Under a represented send-state map, `send_single_cmessage` follows the concrete source-body sequence/update branch. -/
def spec_send_single_cmessage_matches_send_single_message (impl : RepoImpl) : Prop :=
  ∀ (self : CSingleDelivery) (m : CMessage) (dst : EndPoint)
      (ghostLookup : AbstractEndPoint → Option CAckState),
    valid_L337 self = true →
    cMessageAbstractableModel m = true →
    messageMarshallableModel m = true →
    cMessageGeneratedWireMarshalableModel m = true →
    endpointMarshallableModel dst = true →
    endpointGeneratedWireMarshalableModel dst = true →
    endpointHashmapEntriesRepresentMap self.send_state.epmap.entries ghostLookup →
    let out := impl.verifiedIronkv.send_single_cmessage self m dst
    let oldAck := (ghostLookup (ioTView dst)).getD defaultCAckState
    let newSeqno := oldAck.num_packets_acked + oldAck.un_acked.length + 1
    if newSeqno > 18446744073709551615 then
      out.1 = self ∧ out.2 = none
    else
      let msg := CSingleMessage.Message newSeqno dst m
      let newAck := { oldAck with un_acked := oldAck.un_acked ++ [msg] }
      valid_L337 out.1 = true ∧
      out.1.receive_state = self.receive_state ∧
      out.1.send_state.epmap.entries =
        endpointEntriesSet self.send_state.epmap.entries (ioTView dst) newAck ∧
      out.2 = some msg

/-- `retransmit_un_acked_packets` returns the concrete source-body packet list projection with basic packet-shape obligations. -/
def spec_retransmit_un_acked_packets_matches_unacked_messages (impl : RepoImpl) : Prop :=
  ∀ (self : CSingleDelivery) (src : EndPoint),
    valid_L337 self = true →
    endpointMarshallableModel src = true →
    let packets := impl.verifiedIronkv.retransmit_un_acked_packets self src
    packets = unackedPacketsModel self src ∧
    packetsAllFrom packets src ∧
    packetsAllMessagesValid packets ∧
    packetsAllOutboundValid packets
