import VerifiedIronkv.Impl.HostImplT
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedIronkv.Impl.SingleDeliveryModelV

Translated Verus vocabulary and reference implementations for `SingleDeliveryModelV`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

inductive ReceiveImplResult where
  | FreshPacket (ack : CPacket)
  | DuplicatePacket (ack : CPacket)
  | AckOrInvalid
  deriving Repr, DecidableEq, BEq, Inhabited

def cpacketView (p : CPacket) : Packet :=
  { dst := ioTView p.dst, src := ioTView p.src, msg := view_L218 p.msg }

def cAckStateView (x : CAckState) : AckState Message :=
  { num_packets_acked := x.num_packets_acked, un_acked := x.un_acked.map view_L218 }

def cTombstoneTableView (x : CTombstoneTable) : TombstoneTable :=
  x.epmap.entries

def cSendStateView (x : CSendState) : SendState Message :=
  x.epmap.entries.map (fun kv => (kv.1, cAckStateView kv.2))

def cSingleDeliveryView (x : CSingleDelivery) : SingleDelivery Message :=
  { receive_state := cTombstoneTableView x.receive_state, send_state := cSendStateView x.send_state }

def tombstoneLookup (src : AbstractEndPoint) (t : TombstoneTable) : Nat :=
  match endpointHashmapTGet_spec t src with
  | some n => n
  | none => 0

def tombstoneTableLookupConcrete (table : CTombstoneTable) (src : EndPoint) : Nat :=
  match endpointHashmapTGet_spec table.epmap.entries (ioTView src) with
  | some n => n
  | none => 0

def tombstoneTableLookupViewBridge (table : CTombstoneTable) (src : EndPoint) : Prop :=
  endpointHashmapEntriesAreMapLike table.epmap.entries ∧
  tombstoneLookup (ioTView src) (cTombstoneTableView table) =
    tombstoneTableLookupConcrete table src

def endpointEntriesSet {V : Type} [DecidableEq AbstractEndPoint] (entries : List (AbstractEndPoint × V)) (key : AbstractEndPoint) (value : V) : List (AbstractEndPoint × V) :=
  endpointHashmapEntriesSet entries key value

def cTombstoneTableInsertViewBridge
    (pre post : CTombstoneTable) (src : EndPoint) (newLastSeqno : Nat) : Prop :=
  tombstoneTableValid pre = true →
  endpointMarshallableModel src = true →
  post.epmap.entries = endpointEntriesSet pre.epmap.entries (ioTView src) newLastSeqno →
    endpointHashmapEntriesAreMapLike pre.epmap.entries ∧
    endpointHashmapEntriesAreMapLike post.epmap.entries ∧
    (∃ oldLookup,
      endpointHashmapInsertEntriesBridge pre.epmap.entries post.epmap.entries oldLookup (ioTView src) newLastSeqno) ∧
    cTombstoneTableView post =
      endpointEntriesSet (cTombstoneTableView pre) (ioTView src) newLastSeqno

def defaultCAckState : CAckState :=
  { num_packets_acked := 0, un_acked := [] }

def ackStateLookup (sendState : CSendState) (dst : AbstractEndPoint) : CAckState :=
  match endpointHashmapTGet_spec sendState.epmap.entries dst with
  | some ack => ack
  | none => defaultCAckState

def defaultAckState : AckState Message :=
  { num_packets_acked := 0, un_acked := [] }

def ackStateLookupAbstract (sendState : SendState Message) (dst : AbstractEndPoint) : AckState Message :=
  match endpointHashmapTGet_spec sendState dst with
  | some ack => ack
  | none => defaultAckState

def cSendStateLookupViewBridge (sendState : CSendState) (dst : AbstractEndPoint) : Prop :=
  endpointHashmapEntriesAreMapLike sendState.epmap.entries ∧
  endpointHashmapEntriesAreMapLike (cSendStateView sendState) ∧
  (∃ lookup, endpointHashmapMapValuesEntriesBridge sendState.epmap.entries lookup cAckStateView) ∧
  endpointHashmapTGet_spec (cSendStateView sendState) dst =
    Option.map cAckStateView (endpointHashmapTGet_spec sendState.epmap.entries dst) ∧
  cAckStateView (ackStateLookup sendState dst) =
    ackStateLookupAbstract (cSendStateView sendState) dst

def singleDeliveryNewSingleMessage (self : SingleDelivery Message) (pkt : Packet) : Bool :=
  match pkt.msg with
  | SingleMessage.Message seqno _ _ => decide (seqno = tombstoneLookup pkt.src self.receive_state + 1)
  | _ => false

def singleDeliveryShouldAckSingleMessage (self : SingleDelivery Message) (pkt : Packet) : Bool :=
  match pkt.msg with
  | SingleMessage.Message seqno _ _ => decide (seqno ≤ tombstoneLookup pkt.src self.receive_state)
  | _ => false

def singleDeliveryReceiveRealPacket (pre post : SingleDelivery Message) (pkt : Packet) : Prop :=
  if singleDeliveryNewSingleMessage pre pkt then
    post = { pre with receive_state := endpointEntriesSet pre.receive_state pkt.src (tombstoneLookup pkt.src pre.receive_state + 1) }
  else
    post = pre

def packetSetExtEq (xs ys : List Packet) : Prop :=
  ∀ p : Packet, p ∈ xs ↔ p ∈ ys

def packetSetEmpty (xs : List Packet) : Prop :=
  ∀ p : Packet, p ∉ xs

def packetSetSingleton (xs : List Packet) (pkt : Packet) : Prop :=
  ∀ p : Packet, p ∈ xs ↔ p = pkt

def singleDeliverySendAck (_self : SingleDelivery Message) (pkt ack : Packet) (acks : List Packet) : Prop :=
  match pkt.msg, ack.msg with
  | SingleMessage.Message seqno _ _, SingleMessage.Ack ackSeqno =>
      ackSeqno = seqno ∧ ack.src = pkt.dst ∧ ack.dst = pkt.src ∧ packetSetSingleton acks ack
  | _, _ => False

def singleDeliveryMaybeAckPacket (pre : SingleDelivery Message) (pkt ack : Packet) (acks : List Packet) : Prop :=
  if singleDeliveryShouldAckSingleMessage pre pkt then
    singleDeliverySendAck pre pkt ack acks
  else
    packetSetEmpty acks

def newSingleMessageModel (self : CSingleDelivery) (pkt : CPacket) : Bool :=
  singleDeliveryNewSingleMessage (cSingleDeliveryView self) (cpacketView pkt)

def newImplConcreteModel (self : CSingleDelivery) (pkt : CPacket) : Bool :=
  match pkt.msg with
  | CSingleMessage.Message seqno _ _ =>
      generatedU64Valid seqno &&
      decide (seqno > 0) &&
        decide (seqno - 1 = tombstoneTableLookupConcrete self.receive_state pkt.src)
  | _ => false

def shouldAckSingleMessageModel (self : CSingleDelivery) (pkt : CPacket) : Bool :=
  singleDeliveryShouldAckSingleMessage (cSingleDeliveryView self) (cpacketView pkt)

def shouldAckConcreteModel (self : CSingleDelivery) (pkt : CPacket) : Bool :=
  match pkt.msg with
  | CSingleMessage.Message seqno _ _ =>
      generatedU64Valid seqno &&
      decide (seqno ≤ tombstoneTableLookupConcrete self.receive_state pkt.src)
  | _ => false

def cPacketAbstractableModel (pkt : CPacket) : Bool :=
  endpointMarshallableModel pkt.dst &&
  endpointMarshallableModel pkt.src &&
  cSingleMessageAbstractableModel pkt.msg

def shouldAckConcreteProtocolBridge (self : CSingleDelivery) (pkt : CPacket) : Prop :=
  valid_L337 self = true →
  cPacketAbstractableModel pkt = true →
  tombstoneTableLookupViewBridge self.receive_state pkt.src ∧
    shouldAckConcreteModel self pkt =
      singleDeliveryShouldAckSingleMessage (cSingleDeliveryView self) (cpacketView pkt)

def singleDeliveryNewMessageViewBridge (self : CSingleDelivery) (pkt : CPacket) : Prop :=
  valid_L337 self = true →
  cPacketAbstractableModel pkt = true →
  tombstoneTableLookupViewBridge self.receive_state pkt.src ∧
    newImplConcreteModel self pkt =
      singleDeliveryNewSingleMessage (cSingleDeliveryView self) (cpacketView pkt)

def outboundPacketIsValidModel (pkt : CPacket) : Bool :=
  cPacketAbstractableModel pkt &&
  cSingleMessageGeneratedWireMarshalableModel pkt.msg &&
  match pkt.msg with
  | CSingleMessage.InvalidMessage => false
  | _ => true

def validAckPacket (ack pkt : CPacket) : Prop :=
  match view_L218 ack.msg, view_L218 pkt.msg with
  | SingleMessage.Ack ackSeqno, SingleMessage.Message seqno _ _ =>
      ackSeqno = seqno ∧
      cPacketAbstractableModel ack = true ∧
      outboundPacketIsValidModel ack = true ∧
      ioTView ack.src = ioTView pkt.dst ∧
      ioTView ack.dst = ioTView pkt.src
  | _, _ => False

def optionCpacketToPacketList : Option CPacket → List Packet
  | some pkt => [cpacketView pkt]
  | none => []

def optionCpacketToPacketListSetSemantics (opt : Option CPacket) : Prop :=
  match opt with
  | some pkt => packetSetSingleton (optionCpacketToPacketList opt) (cpacketView pkt)
  | none => packetSetEmpty (optionCpacketToPacketList opt)

def receiveImplResultAck : ReceiveImplResult → Option CPacket
  | ReceiveImplResult.FreshPacket ack => some ack
  | ReceiveImplResult.DuplicatePacket ack => some ack
  | ReceiveImplResult.AckOrInvalid => none

def receiveImplResultAbstractedAckSet (rr : ReceiveImplResult) : List Packet :=
  optionCpacketToPacketList (receiveImplResultAck rr)

def receiveImplResultAbstractedAckSetSemantics (rr : ReceiveImplResult) : Prop :=
  match rr with
  | ReceiveImplResult.FreshPacket ack =>
      packetSetSingleton (receiveImplResultAbstractedAckSet rr) (cpacketView ack)
  | ReceiveImplResult.DuplicatePacket ack =>
      packetSetSingleton (receiveImplResultAbstractedAckSet rr) (cpacketView ack)
  | ReceiveImplResult.AckOrInvalid =>
      packetSetEmpty (receiveImplResultAbstractedAckSet rr)

def packetsAllFrom (packets : List CPacket) (src : EndPoint) : Prop :=
  ∀ pkt, pkt ∈ packets → ioTView pkt.src = ioTView src

def receiveRealPacketModel (pre post : CSingleDelivery) (pkt : CPacket) : Prop :=
  singleDeliveryReceiveRealPacket (cSingleDeliveryView pre) (cSingleDeliveryView post) (cpacketView pkt)

def receiveRealPacketConcreteModel (pre post : CSingleDelivery) (pkt : CPacket) : Prop :=
  match view_L218 pkt.msg with
  | SingleMessage.Message _ _ _ =>
      if newImplConcreteModel pre pkt then
        let lastSeqno := tombstoneTableLookupConcrete pre.receive_state pkt.src
        post = { pre with receive_state := { epmap := { entries := endpointEntriesSet pre.receive_state.epmap.entries (ioTView pkt.src) (lastSeqno + 1) } } }
      else
        post = pre
  | _ => post = pre

def receiveRealPacketTombstoneUpdateViewBridge
    (pre post : CSingleDelivery) (pkt : CPacket) : Prop :=
  valid_L337 pre = true →
  cPacketAbstractableModel pkt = true →
  receiveRealPacketConcreteModel pre post pkt →
    match view_L218 pkt.msg with
    | SingleMessage.Message _ _ _ =>
        if newImplConcreteModel pre pkt then
          let lastSeqno := tombstoneTableLookupConcrete pre.receive_state pkt.src
          cTombstoneTableInsertViewBridge pre.receive_state post.receive_state pkt.src (lastSeqno + 1)
        else
          post.receive_state = pre.receive_state
    | _ => post.receive_state = pre.receive_state

def receiveRealPacketConcreteViewBridge (pre post : CSingleDelivery) (pkt : CPacket) : Prop :=
  valid_L337 pre = true →
  cPacketAbstractableModel pkt = true →
  receiveRealPacketConcreteModel pre post pkt →
    singleDeliveryNewMessageViewBridge pre pkt ∧
    receiveRealPacketTombstoneUpdateViewBridge pre post pkt ∧
    tombstoneTableLookupViewBridge pre.receive_state pkt.src ∧
    newImplConcreteModel pre pkt =
      singleDeliveryNewSingleMessage (cSingleDeliveryView pre) (cpacketView pkt) ∧
    receiveRealPacketModel pre post pkt

def maybeAckPacketModel (self : CSingleDelivery) (pkt : CPacket) : Option CPacket :=
  match view_L218 pkt.msg with
  | SingleMessage.Message seqno _ _ =>
      if shouldAckConcreteModel self pkt then
        some { dst := pkt.src, src := pkt.dst, msg := CSingleMessage.Ack seqno }
      else none
  | _ => none

def maybeAckPacketModelAckSetSemantics (self : CSingleDelivery) (pkt : CPacket) : Prop :=
  optionCpacketToPacketListSetSemantics (maybeAckPacketModel self pkt)

def sendSingleCMessageModel (pre post : CSingleDelivery) (m : CMessage) (dst : EndPoint) (sm : Option CSingleMessage) : Prop :=
  let oldAck := ackStateLookup pre.send_state (ioTView dst)
  let newSeqno := oldAck.num_packets_acked + oldAck.un_acked.length + 1
  if newSeqno > 18446744073709551615 then
    post = pre ∧ sm = none
  else
    let msg := CSingleMessage.Message newSeqno dst m
    let newAck := { oldAck with un_acked := oldAck.un_acked ++ [msg] }
    valid_L337 post = true ∧
    post.receive_state = pre.receive_state ∧
    post.send_state.epmap.entries = endpointEntriesSet pre.send_state.epmap.entries (ioTView dst) newAck ∧
    sm = some msg

def singleDeliveryStaticParamsModel : AbstractParameters :=
  { max_seqno := 18446744073709551615,
    max_delegations := 9223372036854775807 }

def singleDeliverySendSingleMessageSourceModel
    (pre post : SingleDelivery Message) (m : Message)
    (dst : AbstractEndPoint) (sm : Option (SingleMessage Message))
    (params : AbstractParameters) : Prop :=
  let oldAck := ackStateLookupAbstract pre.send_state dst
  let newSeqno := oldAck.num_packets_acked + oldAck.un_acked.length + 1
  if newSeqno > params.max_seqno then
    post = pre ∧ sm = none
  else
    let msg := SingleMessage.Message newSeqno dst m
    let newAck := { oldAck with un_acked := oldAck.un_acked ++ [msg] }
    sm = some msg ∧
    post = { pre with send_state := endpointEntriesSet pre.send_state dst newAck }

def cAckStateAppendViewBridge (oldAck : CAckState) (msg : CSingleMessage) : Prop :=
  cAckStateView { oldAck with un_acked := oldAck.un_acked ++ [msg] } =
    { cAckStateView oldAck with un_acked := (cAckStateView oldAck).un_acked ++ [view_L218 msg] }

def cSendStatePutViewBridge
    (pre post : CSendState) (dst : AbstractEndPoint) (newAck : CAckState) : Prop :=
  endpointHashmapEntriesAreMapLike pre.epmap.entries →
  post.epmap.entries = endpointEntriesSet pre.epmap.entries dst newAck →
    endpointHashmapEntriesAreMapLike post.epmap.entries ∧
    (∃ oldLookup,
      endpointHashmapPutEntriesBridge pre.epmap.entries post.epmap.entries oldLookup dst newAck) ∧
    cSendStateView post = endpointEntriesSet (cSendStateView pre) dst (cAckStateView newAck)

def cSendStateSwapThenPutViewBridge
    (pre post : CSendState) (dst : AbstractEndPoint) (finalAck : CAckState) : Prop :=
  let oldAck := ackStateLookup pre dst
  ∃ oldLookup swappedEntries,
    endpointHashmapEntriesRepresentMap pre.epmap.entries oldLookup ∧
    oldAck = (oldLookup dst).getD defaultCAckState ∧
    swappedEntries = endpointEntriesSet pre.epmap.entries dst defaultCAckState ∧
    endpointHashmapSwapEntriesBridge
      pre.epmap.entries swappedEntries oldLookup dst defaultCAckState oldAck defaultCAckState ∧
    endpointHashmapPutEntriesBridge
      swappedEntries post.epmap.entries
      (endpointHashmapGhostLookupInsert oldLookup dst defaultCAckState)
      dst finalAck ∧
    cSendStateView post =
      endpointEntriesSet (cSendStateView pre) dst (cAckStateView finalAck)

def sendSingleCMessageUpdateViewBridge
    (pre post : CSingleDelivery) (m : CMessage) (dst : EndPoint)
    (sm : Option CSingleMessage) : Prop :=
  let oldAck := ackStateLookup pre.send_state (ioTView dst)
  let newSeqno := oldAck.num_packets_acked + oldAck.un_acked.length + 1
  if newSeqno > 18446744073709551615 then
    post = pre ∧ sm = none
  else
    let msg := CSingleMessage.Message newSeqno dst m
    let newAck := { oldAck with un_acked := oldAck.un_acked ++ [msg] }
    sm = some msg ∧
    cAckStateAppendViewBridge oldAck msg ∧
    cSendStatePutViewBridge pre.send_state post.send_state (ioTView dst) newAck ∧
    cSendStateSwapThenPutViewBridge pre.send_state post.send_state (ioTView dst) newAck

def sendSingleCMessageConcreteViewBridge
    (pre post : CSingleDelivery) (m : CMessage) (dst : EndPoint)
    (sm : Option CSingleMessage) : Prop :=
  sendSingleCMessageModel pre post m dst sm ∧
  sendSingleCMessageUpdateViewBridge pre post m dst sm ∧
  cAckStateView (ackStateLookup pre.send_state (ioTView dst)) =
    ackStateLookupAbstract (cSingleDeliveryView pre).send_state (ioTView dst) ∧
  singleDeliverySendSingleMessageSourceModel
    (cSingleDeliveryView pre) (cSingleDeliveryView post)
    (view_L75 m) (ioTView dst) (Option.map view_L218 sm)
    singleDeliveryStaticParamsModel ∧
  match sm with
  | some csm =>
      cSingleMessageAbstractableModel csm = true ∧
      cSingleMessageGeneratedWireMarshalableModel csm = true ∧
      ∃ seqno, view_L218 csm =
        SingleMessage.Message seqno (ioTView dst) (view_L75 m)
  | none => True

def truncateAckStateModel (ack : CAckState) (ackSeqno : Nat) : CAckState :=
  if ackSeqno ≤ ack.num_packets_acked then ack
  else { ack with num_packets_acked := ackSeqno, un_acked := ack.un_acked.drop (ackSeqno - ack.num_packets_acked) }

def receiveAckImplModel (self : CSingleDelivery) (pkt : CPacket) : CSingleDelivery :=
  match view_L218 pkt.msg with
  | SingleMessage.Ack ackSeqno =>
      if generatedU64Valid ackSeqno then
        let src := ioTView pkt.src
        let oldAck := ackStateLookup self.send_state src
        if ackSeqno > oldAck.num_packets_acked then
          let newAck := truncateAckStateModel oldAck ackSeqno
          { self with send_state := { epmap := { entries := endpointEntriesSet self.send_state.epmap.entries src newAck } } }
        else self
      else self
  | _ => self

def receiveAckModel (pre post : CSingleDelivery) (pkt : CPacket) : Prop :=
  match view_L218 pkt.msg with
  | SingleMessage.Ack ackSeqno =>
      if generatedU64Valid ackSeqno then
        let oldAck :=
          match endpointHashmapTGet_spec pre.send_state.epmap.entries (ioTView pkt.src) with
          | some ack => ack
          | none => { num_packets_acked := 0, un_acked := [] }
        if ackSeqno > oldAck.num_packets_acked then
          let newAck := truncateAckStateModel oldAck ackSeqno
          post.receive_state = pre.receive_state ∧
          endpointHashmapTGet_spec post.send_state.epmap.entries (ioTView pkt.src) = some newAck ∧
          ∀ ep, ep ≠ ioTView pkt.src → endpointHashmapTGet_spec post.send_state.epmap.entries ep = endpointHashmapTGet_spec pre.send_state.epmap.entries ep
        else
          post = pre
      else
        post = pre
  | _ => post = pre

def truncateUnAckListSourceModel : List (SingleMessage Message) → Nat → List (SingleMessage Message)
  | [], _ => []
  | sm :: rest, ackSeqno =>
      match sm with
      | SingleMessage.Message seqno _ _ =>
          if seqno ≤ ackSeqno then truncateUnAckListSourceModel rest ackSeqno else sm :: rest
      | _ => sm :: rest

def truncateAckStateSourceBridge
    (ack : CAckState) (ackSeqno : Nat) (dst : AbstractEndPoint) : Prop :=
  cAckStateValidForDst ack dst = true →
  ack.num_packets_acked ≤ ackSeqno →
  cAckStateView (truncateAckStateModel ack ackSeqno) =
    { cAckStateView ack with
      num_packets_acked := ackSeqno,
      un_acked := truncateUnAckListSourceModel (cAckStateView ack).un_acked ackSeqno }

def singleDeliveryReceiveAckSourceModel
    (pre post : SingleDelivery Message) (pkt : Packet) (acks : List Packet) : Prop :=
  match pkt.msg with
  | SingleMessage.Ack ackSeqno =>
      packetSetEmpty acks ∧
      if generatedU64Valid ackSeqno then
        let oldAck := ackStateLookupAbstract pre.send_state pkt.src
        if ackSeqno > oldAck.num_packets_acked then
          let newAck : AckState Message :=
            { oldAck with
              num_packets_acked := ackSeqno,
              un_acked := truncateUnAckListSourceModel oldAck.un_acked ackSeqno }
          post.send_state = endpointEntriesSet pre.send_state pkt.src newAck
        else
          post = pre
      else
        post = pre
  | _ => False

def receiveAckConcreteViewBridge (pre post : CSingleDelivery) (pkt : CPacket) : Prop :=
  valid_L337 pre = true →
  cPacketAbstractableModel pkt = true →
  receiveAckModel pre post pkt →
    cSendStateLookupViewBridge pre.send_state (ioTView pkt.src) ∧
    (match view_L218 pkt.msg with
    | SingleMessage.Ack ackSeqno =>
        let oldAck := ackStateLookup pre.send_state (ioTView pkt.src)
        generatedU64Valid ackSeqno = true →
        ackSeqno > oldAck.num_packets_acked →
          truncateAckStateSourceBridge oldAck ackSeqno (ioTView pkt.src) ∧
          cSendStateSwapThenPutViewBridge pre.send_state post.send_state (ioTView pkt.src)
            (truncateAckStateModel oldAck ackSeqno)
    | _ => True) ∧
    singleDeliveryReceiveAckSourceModel
      (cSingleDeliveryView pre) (cSingleDeliveryView post) (cpacketView pkt) []

def receiveImplResultModel (pre : CSingleDelivery) (out : CSingleDelivery × ReceiveImplResult) (pkt : CPacket) : Prop :=
  match view_L218 pkt.msg with
  | SingleMessage.Ack _ =>
      out.1 = receiveAckImplModel pre pkt ∧ out.2 = ReceiveImplResult.AckOrInvalid
  | SingleMessage.Message _ _ _ =>
      receiveRealPacketConcreteModel pre out.1 pkt ∧
      match maybeAckPacketModel out.1 pkt with
      | some ack =>
          if newImplConcreteModel pre pkt then
            out.2 = ReceiveImplResult.FreshPacket ack
          else
            out.2 = ReceiveImplResult.DuplicatePacket ack
      | none => out.2 = ReceiveImplResult.AckOrInvalid
  | SingleMessage.InvalidMessage =>
      out.1 = pre ∧ out.2 = ReceiveImplResult.AckOrInvalid

def receiveImplResultSourcePolarity (pre : CSingleDelivery) (pkt : CPacket) : ReceiveImplResult → Prop
  | ReceiveImplResult.FreshPacket _ =>
      singleDeliveryNewSingleMessage (cSingleDeliveryView pre) (cpacketView pkt) = true
  | ReceiveImplResult.DuplicatePacket _ =>
      singleDeliveryNewSingleMessage (cSingleDeliveryView pre) (cpacketView pkt) = false
  | ReceiveImplResult.AckOrInvalid => True

def singleDeliveryMaybeAckFromReceiveResult
    (post : SingleDelivery Message) (pkt : Packet) (rr : ReceiveImplResult) : Prop :=
  match receiveImplResultAck rr with
  | some ack =>
      singleDeliveryMaybeAckPacket post pkt (cpacketView ack)
        (receiveImplResultAbstractedAckSet rr)
  | none =>
      singleDeliveryShouldAckSingleMessage post pkt = false ∧
      packetSetEmpty (receiveImplResultAbstractedAckSet rr)

def singleDeliveryReceiveFromReceiveImplResult
    (pre post : SingleDelivery Message) (pkt : Packet) (rr : ReceiveImplResult) : Prop :=
  match pkt.msg with
  | SingleMessage.Ack _ =>
      singleDeliveryReceiveAckSourceModel pre post pkt
        (receiveImplResultAbstractedAckSet rr)
  | SingleMessage.Message _ _ _ =>
      singleDeliveryReceiveRealPacket pre post pkt ∧
      singleDeliveryMaybeAckFromReceiveResult post pkt rr
  | SingleMessage.InvalidMessage =>
      post = pre ∧ packetSetEmpty (receiveImplResultAbstractedAckSet rr)

def receiveImplConcreteReceiveBridge
    (pre : CSingleDelivery) (out : CSingleDelivery × ReceiveImplResult) (pkt : CPacket) : Prop :=
  valid_L337 pre = true →
  cPacketAbstractableModel pkt = true →
  receiveImplResultModel pre out pkt →
  receiveImplResultAbstractedAckSetSemantics out.2 →
    receiveImplResultSourcePolarity pre pkt out.2 ∧
    singleDeliveryReceiveFromReceiveImplResult
      (cSingleDeliveryView pre) (cSingleDeliveryView out.1) (cpacketView pkt) out.2

def unackedPacketsModel (self : CSingleDelivery) (src : EndPoint) : List CPacket :=
  List.flatMap (fun kv =>
    kv.2.un_acked.filterMap (fun msg =>
      match msg with
      | CSingleMessage.Message _ msgDst _ => some { dst := msgDst, src := src, msg := msg }
      | _ => none)) self.send_state.epmap.entries

def singleDeliveryUnackedMessages (self : SingleDelivery Message) (src : AbstractEndPoint) : List Packet :=
  List.flatMap (fun kv =>
    kv.2.un_acked.filterMap (fun msg =>
      match msg with
      | SingleMessage.Message _ msgDst _ => some { dst := msgDst, src := src, msg := msg }
      | _ => none)) self.send_state

def sourceUnackedPacketViews (self : CSingleDelivery) (src : EndPoint) : List Packet :=
  singleDeliveryUnackedMessages (cSingleDeliveryView self) (ioTView src)

def retransmitUnackedKeysDomainBridge (self : CSingleDelivery) (_src : EndPoint) : Prop :=
  endpointHashmapKeysDomainBridge self.send_state.epmap.entries
    (endpointHashmapEntriesKeys self.send_state.epmap.entries)

def packetViewsExtEq (xs ys : List CPacket) : Prop :=
  ∀ p : Packet, p ∈ xs.map cpacketView ↔ p ∈ ys.map cpacketView

def packetViewsMatchSourceUnacked (packets : List CPacket) (self : CSingleDelivery) (src : EndPoint) : Prop :=
  retransmitUnackedKeysDomainBridge self src ∧
  ∀ p : Packet, p ∈ packets.map cpacketView ↔ p ∈ sourceUnackedPacketViews self src

def packetViewsMatchConcreteUnacked (packets : List CPacket) (self : CSingleDelivery) (src : EndPoint) : Prop :=
  packetViewsExtEq packets (unackedPacketsModel self src)

def packetsAllMessagesValid (packets : List CPacket) : Prop :=
  ∀ pkt, pkt ∈ packets →
    match view_L218 pkt.msg with
    | SingleMessage.Message _ _ _ => True
    | _ => False

def packetsAllOutboundValid (packets : List CPacket) : Prop :=
  ∀ pkt, pkt ∈ packets → outboundPacketIsValidModel pkt = true

namespace Bank

abbrev NewImplSig := CSingleDelivery → CPacket → Bool
abbrev ReceiveRealPacketImplSig := CSingleDelivery → CPacket → CSingleDelivery × Bool
abbrev ShouldAckSigleMessageImplSig := CSingleDelivery → CPacket → Bool
abbrev MaybeAckPacketImplSig := CSingleDelivery → CPacket → Option CPacket
abbrev ReceiveAckImplSig := CSingleDelivery → CPacket → CSingleDelivery
abbrev SendSingleCmessageSig := CSingleDelivery → CMessage → EndPoint → CSingleDelivery × Option CSingleMessage
abbrev RetransmitUnAckedPacketsSig := CSingleDelivery → EndPoint → List CPacket
abbrev ReceiveImplSig := CSingleDelivery → CPacket → CSingleDelivery × ReceiveImplResult

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=new_impl
-- !benchmark @end code_aux def=new_impl

def Bank.new_impl : Bank.NewImplSig :=
-- !benchmark @start code def=new_impl
  fun self pkt => newImplConcreteModel self pkt
-- !benchmark @end code def=new_impl

-- !benchmark @start code_aux def=receive_real_packet_impl
-- !benchmark @end code_aux def=receive_real_packet_impl

def Bank.receive_real_packet_impl : Bank.ReceiveRealPacketImplSig :=
-- !benchmark @start code def=receive_real_packet_impl
  fun self pkt =>
    match view_L218 pkt.msg with
    | SingleMessage.Message _ _ _ =>
        if newImplConcreteModel self pkt then
          let lastSeqno := tombstoneTableLookupConcrete self.receive_state pkt.src
          let post := { self with receive_state := { epmap := { entries := endpointEntriesSet self.receive_state.epmap.entries (ioTView pkt.src) (lastSeqno + 1) } } }
          (post, true)
        else
          (self, false)
    | _ => (self, false)
-- !benchmark @end code def=receive_real_packet_impl

-- !benchmark @start code_aux def=should_ack_sigle_message_impl
-- !benchmark @end code_aux def=should_ack_sigle_message_impl

def Bank.should_ack_sigle_message_impl : Bank.ShouldAckSigleMessageImplSig :=
-- !benchmark @start code def=should_ack_sigle_message_impl
  fun self pkt => shouldAckConcreteModel self pkt
-- !benchmark @end code def=should_ack_sigle_message_impl

-- !benchmark @start code_aux def=maybe_ack_packet_impl
-- !benchmark @end code_aux def=maybe_ack_packet_impl

def Bank.maybe_ack_packet_impl : Bank.MaybeAckPacketImplSig :=
-- !benchmark @start code def=maybe_ack_packet_impl
  maybeAckPacketModel
-- !benchmark @end code def=maybe_ack_packet_impl

-- !benchmark @start code_aux def=receive_ack_impl
-- !benchmark @end code_aux def=receive_ack_impl

def Bank.receive_ack_impl : Bank.ReceiveAckImplSig :=
-- !benchmark @start code def=receive_ack_impl
  receiveAckImplModel
-- !benchmark @end code def=receive_ack_impl

-- !benchmark @start code_aux def=send_single_cmessage
-- !benchmark @end code_aux def=send_single_cmessage

def Bank.send_single_cmessage : Bank.SendSingleCmessageSig :=
-- !benchmark @start code def=send_single_cmessage
  fun self m dst =>
    let oldAck := ackStateLookup self.send_state (ioTView dst)
    let newSeqno := oldAck.num_packets_acked + oldAck.un_acked.length + 1
    if newSeqno > 18446744073709551615 then
      (self, none)
    else
      let msg := CSingleMessage.Message newSeqno dst m
      let newAck := { oldAck with un_acked := oldAck.un_acked ++ [msg] }
      let post := { self with send_state := { epmap := { entries := endpointEntriesSet self.send_state.epmap.entries (ioTView dst) newAck } } }
      (post, some msg)
-- !benchmark @end code def=send_single_cmessage

-- !benchmark @start code_aux def=retransmit_un_acked_packets
-- !benchmark @end code_aux def=retransmit_un_acked_packets

def Bank.retransmit_un_acked_packets : Bank.RetransmitUnAckedPacketsSig :=
-- !benchmark @start code def=retransmit_un_acked_packets
  fun self src => unackedPacketsModel self src
-- !benchmark @end code def=retransmit_un_acked_packets

-- !benchmark @start code_aux def=receive_impl
-- !benchmark @end code_aux def=receive_impl

def Bank.receive_impl : Bank.ReceiveImplSig :=
-- !benchmark @start code def=receive_impl
  fun self pkt =>
    match view_L218 pkt.msg with
    | SingleMessage.Message _ _ _ =>
        let received := Bank.receive_real_packet_impl self pkt
        match Bank.maybe_ack_packet_impl received.1 pkt with
        | some ack =>
            if received.2 then
              (received.1, ReceiveImplResult.FreshPacket ack)
            else
              (received.1, ReceiveImplResult.DuplicatePacket ack)
        | none => (received.1, ReceiveImplResult.AckOrInvalid)
    | SingleMessage.Ack _ =>
        (Bank.receive_ack_impl self pkt, ReceiveImplResult.AckOrInvalid)
    | SingleMessage.InvalidMessage =>
        (self, ReceiveImplResult.AckOrInvalid)
-- !benchmark @end code def=receive_impl
