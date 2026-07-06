import VerifiedIronkv.Impl.SingleMessageT
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedIronkv.Impl.CmessageV

Translated Verus vocabulary and reference implementations for `CmessageV`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

inductive CMessage where
  | GetRequest (k : CKey)
  | SetRequest (k : CKey) (v : Option (List Nat))
  | Reply (k : CKey) (v : Option (List Nat))
  | Redirect (k : CKey) (id : EndPoint)
  | Shard (kr : KeyRange CKey) (recipient : EndPoint)
  | Delegate (range : KeyRange CKey) (h : CKeyHashMap)
  deriving Repr, DecidableEq, BEq, Inhabited

inductive CSingleMessage where
  | Message (seqno : Nat) (dst : EndPoint) (m : CMessage)
  | Ack (ack_seqno : Nat)
  | InvalidMessage
  deriving Repr, DecidableEq, BEq, Inhabited

structure CPacket where
  dst : EndPoint
  src : EndPoint
  msg : CSingleMessage
  deriving Repr, DecidableEq, BEq, Inhabited

def optional_value_view (ov : Option (List Nat)) : Option (List Nat) :=
  ov

def view_L75 : CMessage → Message
  | CMessage.GetRequest k => Message.GetRequest k
  | CMessage.SetRequest k v => Message.SetRequest k (optional_value_view v)
  | CMessage.Reply k v => Message.Reply k (optional_value_view v)
  | CMessage.Redirect k id => Message.Redirect k (ioTView id)
  | CMessage.Shard kr recipient => Message.Shard kr (ioTView recipient)
  | CMessage.Delegate range h => Message.Delegate range h.m

def view_L218 : CSingleMessage → SingleMessage Message
  | CSingleMessage.Message seqno dst m => SingleMessage.Message seqno (ioTView dst) (view_L75 m)
  | CSingleMessage.Ack ack_seqno => SingleMessage.Ack ack_seqno
  | CSingleMessage.InvalidMessage => SingleMessage.InvalidMessage

def valueMarshallableModel (value : List Nat) : Bool :=
  decide (value.length < 1024)

def optionalValueMarshallableModel : Option (List Nat) → Bool
  | some value => valueMarshallableModel value
  | none => true

def endpointMarshallableModel (ep : EndPoint) : Bool :=
  decide (ep.id.length < 1048576)

def keyRangeNonempty {K : Type} [KeyTrait K] (range : KeyRange K) : Bool :=
  keyIteratorLt range.lo range.hi

def cKeyHashMapMarshallableModel (h : CKeyHashMap) : Bool :=
  decide (h.m.length < 62) &&
  decide (List.Nodup (h.m.map Prod.fst)) &&
  h.m.all (fun kv => valueMarshallableModel kv.2)

def messageMarshallableModel : CMessage → Bool
  | CMessage.GetRequest _ => true
  | CMessage.SetRequest _ v => optionalValueMarshallableModel v
  | CMessage.Reply _ v => optionalValueMarshallableModel v
  | CMessage.Redirect _ id => endpointMarshallableModel id
  | CMessage.Shard kr recipient => endpointMarshallableModel recipient && keyRangeNonempty kr
  | CMessage.Delegate range h => keyRangeNonempty range && cKeyHashMapMarshallableModel h

def singleMessageMarshallableModel : CSingleMessage → Bool
  | CSingleMessage.Message _ dst m => endpointMarshallableModel dst && messageMarshallableModel m
  | CSingleMessage.Ack _ => true
  | CSingleMessage.InvalidMessage => false

def generatedByteValid (b : Nat) : Bool :=
  decide (b < 256)

def generatedU64Valid (x : Nat) : Bool :=
  decide (x < 18446744073709551616)

def generatedVecU8Valid (xs : List Nat) : Bool :=
  generatedU64Valid xs.length && xs.all generatedByteValid

def cKeyGeneratedWireMarshalableModel (k : CKey) : Bool :=
  generatedU64Valid k.ukey

def keyIteratorGeneratedWireMarshalableModel (ki : KeyIterator CKey) : Bool :=
  match ki.k with
  | some k => cKeyGeneratedWireMarshalableModel k
  | none => true

def keyRangeGeneratedWireMarshalableModel (range : KeyRange CKey) : Bool :=
  keyIteratorGeneratedWireMarshalableModel range.lo &&
  keyIteratorGeneratedWireMarshalableModel range.hi

def endpointGeneratedWireMarshalableModel (ep : EndPoint) : Bool :=
  generatedVecU8Valid ep.id

def cKeyKVGeneratedWireMarshalableModel (kv : CKeyKV) : Bool :=
  cKeyGeneratedWireMarshalableModel kv.k && generatedVecU8Valid kv.v

def sortedCKeyKVsByGeneratedToVec : List CKeyKV → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
      decide (a.k.ukey < b.k.ukey) && sortedCKeyKVsByGeneratedToVec (b :: rest)

def insertCKeyKVByGeneratedKey (kv : CKeyKV) : List CKeyKV → List CKeyKV
  | [] => [kv]
  | head :: rest =>
      if kv.k.ukey ≤ head.k.ukey then
        kv :: head :: rest
      else
        head :: insertCKeyKVByGeneratedKey kv rest

def sortCKeyKVsByGeneratedKey : List CKeyKV → List CKeyKV
  | [] => []
  | kv :: rest => insertCKeyKVByGeneratedKey kv (sortCKeyKVsByGeneratedKey rest)

def cKeyHashMapGeneratedWireToVecSurrogate (h : CKeyHashMap) : List CKeyKV :=
  sortCKeyKVsByGeneratedKey (h.m.map (fun kv => { k := kv.1, v := kv.2 }))

def cKeyKVGeneratedWireSerializedSize (kv : CKeyKV) : Nat :=
  16 + kv.v.length

def cKeyHashMapGeneratedWireSerializedSize (h : CKeyHashMap) : Nat :=
  8 + (cKeyHashMapGeneratedWireToVecSurrogate h).foldl
    (fun acc kv => acc + cKeyKVGeneratedWireSerializedSize kv) 0

def cKeyHashMapGeneratedWireMarshalableModel (h : CKeyHashMap) : Bool :=
  let kvs := cKeyHashMapGeneratedWireToVecSurrogate h
  kvs.all cKeyKVGeneratedWireMarshalableModel &&
  sortedCKeyKVsByGeneratedToVec kvs &&
  decide (cKeyHashMapGeneratedWireSerializedSize h <= 1048576)

def cMessageAbstractableModel : CMessage → Bool
  | CMessage.Redirect _ id => endpointMarshallableModel id
  | CMessage.Shard _ recipient => endpointMarshallableModel recipient
  | _ => true

def cSingleMessageAbstractableModel : CSingleMessage → Bool
  | CSingleMessage.Message _ dst m => endpointMarshallableModel dst && cMessageAbstractableModel m
  | CSingleMessage.Ack _ => true
  | CSingleMessage.InvalidMessage => true

def cMessageGeneratedWireMarshalableModel : CMessage → Bool
  | CMessage.GetRequest k => cKeyGeneratedWireMarshalableModel k
  | CMessage.SetRequest k v =>
      cKeyGeneratedWireMarshalableModel k &&
      match v with | some xs => generatedVecU8Valid xs | none => true
  | CMessage.Reply k v =>
      cKeyGeneratedWireMarshalableModel k &&
      match v with | some xs => generatedVecU8Valid xs | none => true
  | CMessage.Redirect k id =>
      cKeyGeneratedWireMarshalableModel k && endpointGeneratedWireMarshalableModel id
  | CMessage.Shard range recipient =>
      keyRangeGeneratedWireMarshalableModel range && endpointGeneratedWireMarshalableModel recipient
  | CMessage.Delegate range h =>
      keyRangeGeneratedWireMarshalableModel range && cKeyHashMapGeneratedWireMarshalableModel h

def cSingleMessageGeneratedWireMarshalableModel : CSingleMessage → Bool
  | CSingleMessage.Message seqno dst m =>
      generatedU64Valid seqno &&
      endpointGeneratedWireMarshalableModel dst &&
      cMessageGeneratedWireMarshalableModel m
  | CSingleMessage.Ack ackSeqno => generatedU64Valid ackSeqno
  | CSingleMessage.InvalidMessage => false

namespace Bank

abbrev IsMessageMarshallableSig := CMessage → Bool
abbrev IsMarshallableSig := CSingleMessage → Bool

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=is_message_marshallable
-- !benchmark @end code_aux def=is_message_marshallable

def Bank.is_message_marshallable : Bank.IsMessageMarshallableSig :=
-- !benchmark @start code def=is_message_marshallable
  messageMarshallableModel
-- !benchmark @end code def=is_message_marshallable

-- !benchmark @start code_aux def=is_marshallable
-- !benchmark @end code_aux def=is_marshallable

def Bank.is_marshallable : Bank.IsMarshallableSig :=
-- !benchmark @start code def=is_marshallable
  singleMessageMarshallableModel
-- !benchmark @end code def=is_marshallable
