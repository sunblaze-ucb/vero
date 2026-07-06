import VerifiedIronkv.Impl.SingleDeliveryT
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedIronkv.Impl.SingleDeliveryStateV

Translated Verus vocabulary and reference implementations for `SingleDeliveryStateV`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

structure CAckState where
  num_packets_acked : Nat
  un_acked : List CSingleMessage
  deriving Repr, DecidableEq, BEq, Inhabited

structure CTombstoneTable where
  epmap : HashMap Nat
  deriving Repr, DecidableEq, BEq, Inhabited

structure CSendState where
  epmap : HashMap CAckState
  deriving Repr, DecidableEq, BEq, Inhabited

structure CSingleDelivery where
  receive_state : CTombstoneTable
  send_state : CSendState
  deriving Repr, DecidableEq, BEq, Inhabited

def abstractEndPointValid (ep : AbstractEndPoint) : Bool :=
  decide (ep.id.length < 1048576)

def cSingleMessageUnackedValidAt (msg : CSingleMessage) (numPacketsAcked index : Nat) (dst : AbstractEndPoint) : Bool :=
  match msg with
  | CSingleMessage.Message seqno msgDst _ =>
      decide (seqno = numPacketsAcked + index + 1 ∧ ioTView msgDst = dst) &&
      cSingleMessageAbstractableModel msg &&
      cSingleMessageGeneratedWireMarshalableModel msg
  | _ => false

def cSingleMessagesUnackedValidFrom (msgs : List CSingleMessage) (numPacketsAcked index : Nat) (dst : AbstractEndPoint) : Bool :=
  match msgs with
  | [] => true
  | msg :: rest =>
      cSingleMessageUnackedValidAt msg numPacketsAcked index dst &&
      cSingleMessagesUnackedValidFrom rest numPacketsAcked (index + 1) dst

def valid_list (msgs : List CSingleMessage) (numPacketsAcked : Nat) (dst : AbstractEndPoint) : Bool :=
  decide (numPacketsAcked + msgs.length ≤ 18446744073709551615) &&
  cSingleMessagesUnackedValidFrom msgs numPacketsAcked 0 dst

def cAckStateValidForDst (ack : CAckState) (dst : AbstractEndPoint) : Bool :=
  valid_list ack.un_acked ack.num_packets_acked dst

def tombstoneTableValid (table : CTombstoneTable) : Bool :=
  decide (List.Nodup (table.epmap.entries.map Prod.fst)) &&
  table.epmap.entries.all (fun entry => abstractEndPointValid entry.1)

def cSendStateValid (sendState : CSendState) : Bool :=
  decide (List.Nodup (sendState.epmap.entries.map Prod.fst)) &&
  sendState.epmap.entries.all (fun entry =>
    abstractEndPointValid entry.1 && cAckStateValidForDst entry.2 entry.1)

def valid_L337 (x : CSingleDelivery) : Bool :=
  tombstoneTableValid x.receive_state && cSendStateValid x.send_state

def unackedMessagesExtendRelation (self : CSingleDelivery) (_src dst : AbstractEndPoint) (i : Nat) : Prop :=
  ∃ ack msg,
    endpointHashmapTGet_spec self.send_state.epmap.entries dst = some ack ∧
    ack.un_acked[i]? = some msg ∧
    match msg with
    | CSingleMessage.Message _ msgDst _ => ioTView msgDst = dst
    | _ => False

namespace Bank

abbrev GetSig := CSendState → EndPoint → Option CAckState

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=get
-- !benchmark @end code_aux def=get

def Bank.get : Bank.GetSig :=
-- !benchmark @start code def=get
  fun sendState src =>
    endpointHashmapTGet_spec sendState.epmap.entries (ioTView src)
-- !benchmark @end code def=get
