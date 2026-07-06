import VerifiedIronkv.Impl.VerusExtraCloneV
import VerifiedIronkv.Impl.VerusExtraChooseV
import VerifiedIronkv.Impl.VerusExtraSeqLibV
import VerifiedIronkv.Impl.VerusExtraSetLibExtV
import VerifiedIronkv.Impl.AbstractEndPointT
import VerifiedIronkv.Impl.ArgsT
import VerifiedIronkv.Impl.EnvironmentT
import VerifiedIronkv.Impl.KeysT
import VerifiedIronkv.Impl.AbstractParametersT
import VerifiedIronkv.Impl.AppInterfaceT
import VerifiedIronkv.Impl.IoT
import VerifiedIronkv.Impl.MainT
import VerifiedIronkv.Impl.HashmapT
import VerifiedIronkv.Impl.EndpointHashmapT
import VerifiedIronkv.Impl.DelegationMapT
import VerifiedIronkv.Impl.DelegationMapV
import VerifiedIronkv.Impl.MessageT
import VerifiedIronkv.Impl.AbstractServiceT
import VerifiedIronkv.Impl.SingleMessageT
import VerifiedIronkv.Impl.CmessageV
import VerifiedIronkv.Impl.NetworkT
import VerifiedIronkv.Impl.SingleDeliveryT
import VerifiedIronkv.Impl.SingleDeliveryStateV
import VerifiedIronkv.Impl.NetShtV
import VerifiedIronkv.Impl.HostProtocolT
import VerifiedIronkv.Impl.MarshalV
import VerifiedIronkv.Impl.MarshalIronshtSpecificV
import VerifiedIronkv.Impl.SeqIsUniqueV
import VerifiedIronkv.Impl.HostImplV
import VerifiedIronkv.Impl.HostImplT
import VerifiedIronkv.Impl.SingleDeliveryModelV

/-!
# VerifiedIronkv.Test

`#guard` conformance tests against `Bank.*` reference implementations.

DO NOT MODIFY — infrastructure.
-/

open Bank

#guard Bank.clone_l151 { ukey := 7 } == { ukey := 7 }
#guard Bank.endpoints_contain [{ id := [1, 2, 3] }] { id := [1, 2, 3] } == true
#guard Bank.endpoints_contain [{ id := [1, 2, 3] }] { id := [4] } == false
#guard Bank.test_unique [{ id := [9] }] == true
#guard Bank.test_unique [{ id := [9] }, { id := [9] }] == false
#guard Bank.test_unique [] == true
#guard Bank.endpoints_contain [{ id := [1] }, { id := [2] }] { id := [2] } == true
#guard Bank.is_marshallable (CSingleMessage.Ack 1) == true
#check Bank.send

def testSrc : EndPoint := { id := [1] }
def testDst : EndPoint := { id := [2] }
def testKey : CKey := { ukey := 5 }
def testMessage : CMessage := CMessage.GetRequest testKey
def testEmptyDelivery : CSingleDelivery :=
  { receive_state := { epmap := { entries := [] } }, send_state := { epmap := { entries := [] } } }
def testSeenOneDelivery : CSingleDelivery :=
  { receive_state := { epmap := { entries := [(ioTView testSrc, 1)] } }, send_state := { epmap := { entries := [] } } }
def testPacket : CPacket :=
  { dst := testDst, src := testSrc, msg := CSingleMessage.Message 1 testDst testMessage }
def testSeqZeroPacket : CPacket :=
  { dst := testDst, src := testSrc, msg := CSingleMessage.Message 0 testDst testMessage }
def testSeqTwoPacket : CPacket :=
  { dst := testDst, src := testSrc, msg := CSingleMessage.Message 2 testDst testMessage }
def testFuturePacket : CPacket :=
  { dst := testDst, src := testSrc, msg := CSingleMessage.Message 3 testDst testMessage }
def testAckPacket : CPacket :=
  { dst := testDst, src := testSrc, msg := CSingleMessage.Ack 1 }
def testHugeSeqno : Nat := 18446744073709551616
def testHugeAckPacket : CPacket :=
  { dst := testDst, src := testSrc, msg := CSingleMessage.Ack testHugeSeqno }
def testHugeMessagePacket : CPacket :=
  { dst := testDst, src := testSrc, msg := CSingleMessage.Message testHugeSeqno testDst testMessage }
def testNetClient : NetClient :=
  {
    state := State.Receiving,
    history := [],
    end_point := testSrc,
    c_pointers := { get_time_func := 0, receive_func := 0, send_func := 0 },
    profiler := { last_event := 0, last_report := 0, event_counter := [] }
  }
def testSendOkPost : NetClient :=
  { testNetClient with
    state := State.Sending,
    history := [LIoOp.Send { dst := ioTView testDst, src := ioTView testSrc, msg := [9, 8] }] }
def testSendError : IronfleetIOError := { message := "Failed to send" }
def testSendErrorPost : NetClient :=
  { testNetClient with state := State.Error }
def testLo : KeyIterator CKey := { k := some { ukey := 0 } }
def testMid : KeyIterator CKey := { k := some { ukey := 5 } }
def testHi : KeyIterator CKey := { k := some { ukey := 10 } }
def testEnd : KeyIterator CKey := { k := none }
def testOutsideKey : CKey := { ukey := 12 }
def testDelegationBase : DelegationMap CKey := Bank.new_l1053 ({ ukey := 0 } : CKey) testSrc
def testDelegationSet : DelegationMap CKey := Bank.set_l1115 testDelegationBase testLo testHi testDst
def testDelegationHiExclusive : DelegationMap CKey :=
  { lows := strictlyOrderedMapFromEntries [({ ukey := 0 }, testSrc), ({ ukey := 10 }, testDst)],
    m := delegationGhostMapTotal (ioTView testSrc),
    default := ioTView testSrc,
    overrides := [],
    ranges := [] }
def testDelegationInteriorDisagree : DelegationMap CKey :=
  { lows := strictlyOrderedMapFromEntries [({ ukey := 0 }, testSrc), ({ ukey := 5 }, testDst), ({ ukey := 10 }, testSrc)],
    m := delegationGhostMapTotal (ioTView testSrc),
    default := ioTView testSrc,
    overrides := [],
    ranges := [] }
def testRange : KeyRange CKey := { lo := testLo, hi := testHi }
def testEmptyRange : KeyRange CKey := { lo := testHi, hi := testLo }
def testHash : CKeyHashMap := { m := [({ ukey := 1 }, [7]), ({ ukey := 2 }, [8])] }
def testDuplicateHash : CKeyHashMap := { m := [({ ukey := 1 }, [7]), ({ ukey := 1 }, [8])] }
def testUnsortedHash : CKeyHashMap := { m := [({ ukey := 2 }, [8]), ({ ukey := 1 }, [7])] }
def testUnsortedHashRawBytes : List Nat :=
  serializeList serializeCKeyKV [{ k := { ukey := 2 }, v := [8] }, { k := { ukey := 1 }, v := [7] }]
def testOverflowDelivery : CSingleDelivery :=
  { receive_state := { epmap := { entries := [] } },
    send_state := { epmap := { entries := [(ioTView testDst, { num_packets_acked := 18446744073709551615, un_acked := [] })] } } }

#guard Bank.valid_physical_address testSrc == true
#guard Bank.valid_physical_address { id := List.replicate 1048576 0 } == false
#guard testSendOkPost.state == State.Sending
#guard testSendOkPost.history == [LIoOp.Send { dst := ioTView testDst, src := ioTView testSrc, msg := [9, 8] }]
#guard testSendErrorPost.state == State.Error
#guard testSendErrorPost.history == testNetClient.history
#guard testSendError.message == "Failed to send"
#guard Bank.get_l1102 testDelegationBase testKey == testSrc
#guard Bank.get_l1102 (Bank.new_l1053 ({ ukey := 0 } : CKey) testDst) ({ ukey := 99 } : CKey) == testDst
#guard Bank.get_l1102 testDelegationSet testKey == testDst
#guard Bank.get_l1102 testDelegationSet testOutsideKey == testSrc
#guard Bank.set_l1115 testDelegationBase testHi testLo testDst == testDelegationBase
#guard testDelegationBase.m == delegationGhostMapTotal (ioTView testSrc)
#guard testDelegationSet.m == delegationGhostMapSetRange testDelegationBase.m testLo testHi testDst
#guard delegationMapSourceGhostViewOf testDelegationSet testKey == ioTView testDst
#guard delegationMapSourceGhostViewOf testDelegationSet testOutsideKey == ioTView testSrc
#guard testDelegationSet.ranges == [{ lo := testLo, hi := testHi, dst := ioTView testDst }]
#guard (Bank.set_l1115 testDelegationSet testHi testLo testSrc).ranges == testDelegationSet.ranges
#guard Bank.range_consistent_impl testDelegationSet testLo testHi testDst == true
#guard Bank.delegate_for_key_range_is_host_impl testDelegationSet testLo testHi testDst == true
#guard Bank.range_consistent_impl testDelegationHiExclusive testLo testHi testSrc == true
#guard Bank.range_consistent_impl testDelegationInteriorDisagree testLo testHi testSrc == false
#guard Bank.range_consistent_impl testDelegationHiExclusive testLo testEnd testSrc == false
#guard Bank.is_message_marshallable (CMessage.SetRequest testKey (some [1, 2])) == true
#guard Bank.is_message_marshallable (CMessage.SetRequest testKey (some (List.replicate 1024 0))) == false
#guard Bank.is_message_marshallable (CMessage.Reply testKey none) == true
#guard Bank.is_message_marshallable (CMessage.Redirect testKey testDst) == true
#guard Bank.is_message_marshallable (CMessage.Shard testRange testDst) == true
#guard Bank.is_message_marshallable (CMessage.Shard testEmptyRange testDst) == false
#guard Bank.is_message_marshallable (CMessage.Delegate testRange testHash) == true
#guard Bank.is_message_marshallable (CMessage.Delegate testRange testDuplicateHash) == false
#guard Bank.is_marshallable (CSingleMessage.Message 1 testDst (CMessage.SetRequest testKey (some (List.replicate 1024 0)))) == false
#guard cSingleMessageGeneratedWireMarshalableModel (CSingleMessage.Ack testHugeSeqno) == false
#guard cSingleMessageGeneratedWireMarshalableModel testHugeMessagePacket.msg == false
#guard cMessageGeneratedWireMarshalableModel (CMessage.GetRequest { ukey := testHugeSeqno }) == false
#guard Bank.sht_demarshall_data_method (cSingleMessageSerialize (CSingleMessage.Ack 7)) == CSingleMessage.Ack 7
#guard Bank.sht_demarshall_data_method (cSingleMessageSerialize (CSingleMessage.Ack 7) ++ [0]) == CSingleMessage.InvalidMessage
#guard Bank.sht_demarshall_data_method [9, 0] == CSingleMessage.InvalidMessage
#guard Bank.sht_demarshall_data_method [1, 256, 0, 0, 0, 0, 0, 0, 0] == CSingleMessage.InvalidMessage
#guard Bank.sht_demarshall_data_method (cSingleMessageSerialize (CSingleMessage.Message 1 testDst testMessage)) == CSingleMessage.Message 1 testDst testMessage
#guard Bank.sht_demarshall_data_method (cSingleMessageSerialize (CSingleMessage.Message 2 testDst (CMessage.SetRequest testKey (some [3, 4])))) == CSingleMessage.Message 2 testDst (CMessage.SetRequest testKey (some [3, 4]))
#guard Bank.sht_demarshall_data_method (cSingleMessageSerialize (CSingleMessage.Message 3 testDst (CMessage.Reply testKey none))) == CSingleMessage.Message 3 testDst (CMessage.Reply testKey none)
#guard Bank.sht_demarshall_data_method (cSingleMessageSerialize (CSingleMessage.Message 4 testDst (CMessage.Redirect testKey testSrc))) == CSingleMessage.Message 4 testDst (CMessage.Redirect testKey testSrc)
#guard Bank.sht_demarshall_data_method (cSingleMessageSerialize (CSingleMessage.Message 5 testDst (CMessage.Shard testRange testSrc))) == CSingleMessage.Message 5 testDst (CMessage.Shard testRange testSrc)
#guard Bank.sht_demarshall_data_method (cSingleMessageSerialize (CSingleMessage.Message 6 testDst (CMessage.Delegate testRange testHash))) == CSingleMessage.Message 6 testDst (CMessage.Delegate testRange testHash)
#guard Bank.sht_demarshall_data_method (cSingleMessageSerialize (CSingleMessage.Message 7 testDst (CMessage.Delegate testRange testUnsortedHash))) == CSingleMessage.Message 7 testDst (CMessage.Delegate testRange testHash)
#guard parseCKeyHashMap testUnsortedHashRawBytes 0 == none
#guard Bank.sht_demarshall_data_method (cSingleMessageSerialize (CSingleMessage.Message 8 testDst (CMessage.SetRequest testKey (some [256])))) == CSingleMessage.InvalidMessage
#guard Bank.sht_demarshall_data_method (cSingleMessageSerialize (CSingleMessage.Message 9 testDst (CMessage.SetRequest testKey (some (List.replicate 1024 0))))) == CSingleMessage.Message 9 testDst (CMessage.SetRequest testKey (some (List.replicate 1024 0)))
#guard (Bank.receive_real_packet_impl testEmptyDelivery testPacket).2 == true
#guard endpointHashmapTGet_spec (Bank.receive_real_packet_impl testEmptyDelivery testPacket).1.receive_state.epmap.entries (ioTView testSrc) == some 1
#guard Bank.new_impl testEmptyDelivery testPacket == true
#guard Bank.new_impl testEmptyDelivery testSeqZeroPacket == false
#guard Bank.new_impl testSeenOneDelivery testPacket == false
#guard Bank.new_impl testSeenOneDelivery testSeqTwoPacket == true
#guard (Bank.receive_real_packet_impl testSeenOneDelivery testPacket).2 == false
#guard (Bank.receive_real_packet_impl testSeenOneDelivery testPacket).1 == testSeenOneDelivery
#guard endpointHashmapTGet_spec (Bank.receive_real_packet_impl testSeenOneDelivery testSeqTwoPacket).1.receive_state.epmap.entries (ioTView testSrc) == some 2
#guard
  match Bank.maybe_ack_packet_impl testSeenOneDelivery testPacket with
  | some ack => ack.dst == testSrc && ack.src == testDst && ack.msg == CSingleMessage.Ack 1
  | none => false
#guard Bank.should_ack_sigle_message_impl testEmptyDelivery testFuturePacket == false
#guard Bank.should_ack_sigle_message_impl testSeenOneDelivery testHugeMessagePacket == false
#guard Bank.maybe_ack_packet_impl testEmptyDelivery testFuturePacket == none
#guard Bank.maybe_ack_packet_impl testSeenOneDelivery testHugeMessagePacket == none
#guard
  let post := (Bank.receive_real_packet_impl testEmptyDelivery testPacket).1
  Bank.should_ack_sigle_message_impl post testPacket == true
#guard
  let post := (Bank.receive_real_packet_impl testEmptyDelivery testPacket).1
  match Bank.maybe_ack_packet_impl post testPacket with
  | some ack =>
      match ack.msg with
      | CSingleMessage.Ack 1 => ack.src == testDst && ack.dst == testSrc
      | _ => false
  | none => false
#guard
  match (Bank.receive_impl testEmptyDelivery testPacket).2 with
  | ReceiveImplResult.FreshPacket ack =>
      match ack.msg with
      | CSingleMessage.Ack 1 => ack.src == testDst && ack.dst == testSrc
      | _ => false
  | _ => false
#guard
  let post := (Bank.receive_real_packet_impl testEmptyDelivery testPacket).1
  match (Bank.receive_impl post testPacket).2 with
  | ReceiveImplResult.DuplicatePacket ack =>
      match ack.msg with
      | CSingleMessage.Ack 1 => ack.src == testDst && ack.dst == testSrc
      | _ => false
  | _ => false
#guard
  match (Bank.receive_impl testEmptyDelivery testAckPacket).2 with
  | ReceiveImplResult.AckOrInvalid => true
  | _ => false
#guard Bank.receive_ack_impl testEmptyDelivery testHugeAckPacket == testEmptyDelivery
#guard Bank.receive_impl testEmptyDelivery testHugeAckPacket == (testEmptyDelivery, ReceiveImplResult.AckOrInvalid)
#guard
  let invalidPacket := { testPacket with msg := CSingleMessage.InvalidMessage }
  Bank.receive_impl testEmptyDelivery invalidPacket == (testEmptyDelivery, ReceiveImplResult.AckOrInvalid)
#guard
  match Bank.send_single_cmessage testEmptyDelivery testMessage testDst with
  | (post, some (CSingleMessage.Message 1 _ _)) =>
      match endpointHashmapTGet_spec post.send_state.epmap.entries (ioTView testDst) with
      | some ack => ack.un_acked.length == 1
      | none => false
  | _ => false
#guard
  match Bank.send_single_cmessage testEmptyDelivery testMessage testDst with
  | (post, some _) =>
      match Bank.get post.send_state testDst with
      | some ack => ack.un_acked.length == 1
      | none => false
  | _ => false
#guard
  match Bank.send_single_cmessage testEmptyDelivery testMessage testDst with
  | (post, some _) => (Bank.retransmit_un_acked_packets post testSrc).length == 1
  | _ => false
#guard Bank.send_single_cmessage testOverflowDelivery testMessage testDst == (testOverflowDelivery, none)
#guard
  let post := Bank.receive_ack_impl (Bank.send_single_cmessage testEmptyDelivery testMessage testSrc).1 testAckPacket
  match Bank.get post.send_state testSrc with
  | some ack => ack.num_packets_acked == 1 && ack.un_acked == []
  | none => false
#guard
  let sent := (Bank.send_single_cmessage testEmptyDelivery testMessage testSrc).1
  match Bank.receive_impl sent testAckPacket with
  | (post, ReceiveImplResult.AckOrInvalid) =>
      match Bank.get post.send_state testSrc with
      | some ack => ack.num_packets_acked == 1 && ack.un_acked == []
      | none => false
  | _ => false
#guard
  match Bank.get (Bank.receive_ack_impl testEmptyDelivery testAckPacket).send_state testSrc with
  | some ack => ack.num_packets_acked == 1 && ack.un_acked == []
  | none => false
#guard
  optionCpacketToPacketList (some testPacket) == [cpacketView testPacket] &&
  optionCpacketToPacketList none == []
#guard
  receiveImplResultAck (ReceiveImplResult.FreshPacket testPacket) == some testPacket &&
  receiveImplResultAck ReceiveImplResult.AckOrInvalid == none
#guard
  let longMsg := CSingleMessage.Message 10 testDst (CMessage.SetRequest testKey (some (List.replicate 1024 0)))
  cSingleMessageGeneratedWireMarshalableModel longMsg == true &&
  singleMessageMarshallableModel longMsg == false &&
  cSingleMessageUnackedValidAt longMsg 9 0 (ioTView testDst) == true
#guard
  match Bank.real_init_impl testNetClient [[1], [2]] with
  | some hs =>
      hs.constants.host_ids.length == 2 &&
      hs.constants.me == testSrc
  | none => false
#guard
  match Bank.real_init_impl testNetClient [[1], [2]] with
  | some hs => hs.next_action_index == 0 && hs.resend_count == 0
  | none => false
#guard
  match Bank.real_init_impl testNetClient [[1], [2]] with
  | some hs =>
      hs.next_action_index < 3 &&
      delegationMapValid hs.delegation_map &&
      (ioTView hs.constants.me == ioTView testSrc) &&
      abstractEndPointValid (ioTView hs.constants.me) &&
      decide (hs.num_delegations < hs.constants.params.max_delegations) &&
      (hs.constants.params == staticParametersModel) &&
      decide (hs.resend_count < 100000000)
  | none => false
#guard
  match Bank.real_init_impl testNetClient [[1], [2]] with
  | some hs =>
      hs.delegation_map.m == delegationGhostMapTotal (ioTView hs.constants.root_identity) &&
      delegationMapSourceGhostViewOf hs.delegation_map testKey == ioTView hs.constants.root_identity
  | none => false
#guard
  match Bank.real_init_impl testNetClient [[1], [2]] with
  | some hs =>
      hs.h.m == [] &&
      hs.sd.receive_state.epmap.entries == [] &&
      hs.sd.send_state.epmap.entries == []
  | none => false
#guard Bank.real_init_impl testNetClient [] == none
#guard Bank.real_init_impl testNetClient [[1], [1]] == none
