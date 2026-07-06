import VerifiedIronkv.Impl.SingleDeliveryStateV
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedIronkv.Impl.NetShtV

Translated Verus vocabulary and reference implementations for `NetShtV`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

inductive ReceiveResult where
  | Fail
  | Timeout
  | Packet (cpacket : CPacket)
  deriving Repr, DecidableEq, BEq, Inhabited

abbrev LSHTPacket := LPacket AbstractEndPoint (SingleMessage Message)

def byteValid (b : Nat) : Bool :=
  decide (b < 256)

def bytesValid (bs : List Nat) : Bool :=
  bs.all byteValid

def natToLeBytesAux : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, x => (x % 256) :: natToLeBytesAux n (x / 256)

def natToU64LeBytes (x : Nat) : List Nat :=
  natToLeBytesAux 8 x

def leBytesToNatAux : List Nat → Nat → Nat
  | [], _ => 0
  | b :: rest, mul => b * mul + leBytesToNatAux rest (mul * 256)

def u64FromLeBytes (bs : List Nat) : Nat :=
  leBytesToNatAux bs 1

def parseByte (data : List Nat) (start : Nat) : Option (Nat × Nat) :=
  match data[start]? with
  | some b => if byteValid b then some (b, start + 1) else none
  | none => none

def parseRawBytes (data : List Nat) (start len : Nat) : Option (List Nat × Nat) :=
  let chunk := (data.drop start).take len
  if decide (chunk.length = len) && bytesValid chunk then some (chunk, start + len) else none

def parseU64 (data : List Nat) (start : Nat) : Option (Nat × Nat) :=
  match parseRawBytes data start 8 with
  | some (bs, next) => some (u64FromLeBytes bs, next)
  | none => none

def parseVecU8 (data : List Nat) (start : Nat) : Option (List Nat × Nat) :=
  match parseU64 data start with
  | some (len, mid) => parseRawBytes data mid len
  | none => none

def parseOption {α : Type} (parse : List Nat → Nat → Option (α × Nat)) (data : List Nat) (start : Nat) : Option (Option α × Nat) :=
  match parseByte data start with
  | some (0, next) => some (none, next)
  | some (1, next) =>
      match parse data next with
      | some (x, endPos) => some (some x, endPos)
      | none => none
  | _ => none

def parseListAux {α : Type} (parse : List Nat → Nat → Option (α × Nat)) : Nat → List Nat → Nat → Option (List α × Nat)
  | 0, _, start => some ([], start)
  | n + 1, data, start =>
      match parse data start with
      | some (x, mid) =>
          match parseListAux parse n data mid with
          | some (xs, endPos) => some (x :: xs, endPos)
          | none => none
      | none => none

def parseList {α : Type} (parse : List Nat → Nat → Option (α × Nat)) (data : List Nat) (start : Nat) : Option (List α × Nat) :=
  match parseU64 data start with
  | some (len, mid) => parseListAux parse len data mid
  | none => none

def serializeOption {α : Type} (serialize : α → List Nat) : Option α → List Nat
  | none => [0]
  | some x => [1] ++ serialize x

def serializeList {α : Type} (serialize : α → List Nat) (xs : List α) : List Nat :=
  natToU64LeBytes xs.length ++ List.flatMap serialize xs

def serializeVecU8 (xs : List Nat) : List Nat :=
  natToU64LeBytes xs.length ++ xs

def serializeSHTKey (k : SHTKey) : List Nat :=
  natToU64LeBytes k.ukey

def parseSHTKey (data : List Nat) (start : Nat) : Option (SHTKey × Nat) :=
  match parseU64 data start with
  | some (x, next) => some ({ ukey := x }, next)
  | none => none

def serializeEndPoint (ep : EndPoint) : List Nat :=
  serializeVecU8 ep.id

def parseEndPoint (data : List Nat) (start : Nat) : Option (EndPoint × Nat) :=
  match parseVecU8 data start with
  | some (id, next) => some ({ id := id }, next)
  | none => none

def serializeKeyIteratorU64 (ki : KeyIterator CKey) : Option Nat :=
  ki.k.map (fun k => k.ukey)

def keyIteratorOfSerialized (x : Option Nat) : KeyIterator CKey :=
  { k := x.map (fun u => { ukey := u }) }

def serializeKeyRangeCKey (kr : KeyRange CKey) : List Nat :=
  serializeOption natToU64LeBytes (serializeKeyIteratorU64 kr.lo) ++
  serializeOption natToU64LeBytes (serializeKeyIteratorU64 kr.hi)

def parseKeyRangeCKey (data : List Nat) (start : Nat) : Option (KeyRange CKey × Nat) :=
  match parseOption parseU64 data start with
  | some (lo, mid) =>
      match parseOption parseU64 data mid with
      | some (hi, endPos) => some ({ lo := keyIteratorOfSerialized lo, hi := keyIteratorOfSerialized hi }, endPos)
      | none => none
  | none => none

def serializeCKeyKV (kv : CKeyKV) : List Nat :=
  serializeSHTKey kv.k ++ serializeVecU8 kv.v

def parseCKeyKV (data : List Nat) (start : Nat) : Option (CKeyKV × Nat) :=
  match parseSHTKey data start with
  | some (k, mid) =>
      match parseVecU8 data mid with
      | some (v, endPos) => some ({ k := k, v := v }, endPos)
      | none => none
  | none => none

def sortedCKeyKVs : List CKeyKV → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.k.ukey < b.k.ukey) && sortedCKeyKVs (b :: rest)

def cKeyHashMapFromKVs (kvs : List CKeyKV) : CKeyHashMap :=
  { m := kvs.map (fun kv => (kv.k, kv.v)) }

def cKeyHashMapToKVs (h : CKeyHashMap) : List CKeyKV :=
  cKeyHashMapGeneratedWireToVecSurrogate h

def serializeCKeyHashMap (h : CKeyHashMap) : List Nat :=
  serializeList serializeCKeyKV (cKeyHashMapToKVs h)

def parseCKeyHashMap (data : List Nat) (start : Nat) : Option (CKeyHashMap × Nat) :=
  match parseList parseCKeyKV data start with
  | some (kvs, endPos) =>
      if sortedCKeyKVs kvs && decide (endPos - start <= 1048576) then
        some (cKeyHashMapFromKVs kvs, endPos)
      else none
  | none => none

def serializeCMessage : CMessage → List Nat
  | CMessage.GetRequest k => [0] ++ serializeSHTKey k
  | CMessage.SetRequest k v => [1] ++ serializeSHTKey k ++ serializeOption serializeVecU8 v
  | CMessage.Reply k v => [2] ++ serializeSHTKey k ++ serializeOption serializeVecU8 v
  | CMessage.Redirect k id => [3] ++ serializeSHTKey k ++ serializeEndPoint id
  | CMessage.Shard kr recipient => [4] ++ serializeKeyRangeCKey kr ++ serializeEndPoint recipient
  | CMessage.Delegate range h => [5] ++ serializeKeyRangeCKey range ++ serializeCKeyHashMap h

def parseCMessage (data : List Nat) (start : Nat) : Option (CMessage × Nat) :=
  match parseByte data start with
  | some (0, mid) =>
      match parseSHTKey data mid with
      | some (k, endPos) => some (CMessage.GetRequest k, endPos)
      | none => none
  | some (1, mid) =>
      match parseSHTKey data mid with
      | some (k, mid) =>
          match parseOption parseVecU8 data mid with
          | some (v, endPos) => some (CMessage.SetRequest k v, endPos)
          | none => none
      | none => none
  | some (2, mid) =>
      match parseSHTKey data mid with
      | some (k, mid) =>
          match parseOption parseVecU8 data mid with
          | some (v, endPos) => some (CMessage.Reply k v, endPos)
          | none => none
      | none => none
  | some (3, mid) =>
      match parseSHTKey data mid with
      | some (k, mid) =>
          match parseEndPoint data mid with
          | some (id, endPos) => some (CMessage.Redirect k id, endPos)
          | none => none
      | none => none
  | some (4, mid) =>
      match parseKeyRangeCKey data mid with
      | some (kr, mid) =>
          match parseEndPoint data mid with
          | some (recipient, endPos) => some (CMessage.Shard kr recipient, endPos)
          | none => none
      | none => none
  | some (5, mid) =>
      match parseKeyRangeCKey data mid with
      | some (range, mid) =>
          match parseCKeyHashMap data mid with
          | some (h, endPos) => some (CMessage.Delegate range h, endPos)
          | none => none
      | none => none
  | _ => none

def cSingleMessageSerialize : CSingleMessage → List Nat
  | CSingleMessage.Message seqno dst m => [0] ++ natToU64LeBytes seqno ++ serializeEndPoint dst ++ serializeCMessage m
  | CSingleMessage.Ack ackSeqno => [1] ++ natToU64LeBytes ackSeqno
  | CSingleMessage.InvalidMessage => [2]

def parseCSingleMessage (data : List Nat) (start : Nat) : Option (CSingleMessage × Nat) :=
  match parseByte data start with
  | some (0, mid) =>
      match parseU64 data mid with
      | some (seqno, mid) =>
          match parseEndPoint data mid with
          | some (dst, mid) =>
              match parseCMessage data mid with
              | some (m, endPos) => some (CSingleMessage.Message seqno dst m, endPos)
              | none => none
          | none => none
      | none => none
  | some (1, mid) =>
      match parseU64 data mid with
      | some (ackSeqno, endPos) => some (CSingleMessage.Ack ackSeqno, endPos)
      | none => none
  | some (2, mid) => some (CSingleMessage.InvalidMessage, mid)
  | _ => none

def acceptedEndpointChecks : CSingleMessage → Bool
  | CSingleMessage.Message _ dst m =>
      endpointMarshallableModel dst &&
      match m with
      | CMessage.Redirect _ id => endpointMarshallableModel id
      | CMessage.Shard _ recipient => endpointMarshallableModel recipient
      | _ => true
  | CSingleMessage.Ack _ => true
  | CSingleMessage.InvalidMessage => false

def wireMarshalableCMessage : CMessage → Bool
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

def wireMarshalableCSingleMessage : CSingleMessage → Bool
  | CSingleMessage.Message seqno dst m =>
      generatedU64Valid seqno &&
      endpointGeneratedWireMarshalableModel dst &&
      wireMarshalableCMessage m
  | CSingleMessage.Ack ackSeqno => generatedU64Valid ackSeqno
  | CSingleMessage.InvalidMessage => false

def shtDemarshallDataModel (buffer : List Nat) : CSingleMessage :=
  match parseCSingleMessage buffer 0 with
  | some (msg, count) =>
      if count = buffer.length then
        if acceptedEndpointChecks msg &&
          wireMarshalableCSingleMessage msg &&
          cSingleMessageGeneratedWireMarshalableModel msg &&
          cSingleMessageAbstractableModel msg then
            msg
          else CSingleMessage.InvalidMessage
      else CSingleMessage.InvalidMessage
  | none => CSingleMessage.InvalidMessage

namespace Bank

abbrev ShtDemarshallDataMethodSig := List Nat → CSingleMessage

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=sht_demarshall_data_method
-- !benchmark @end code_aux def=sht_demarshall_data_method

def Bank.sht_demarshall_data_method : Bank.ShtDemarshallDataMethodSig :=
-- !benchmark @start code def=sht_demarshall_data_method
  shtDemarshallDataModel
-- !benchmark @end code def=sht_demarshall_data_method
