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
# VerifiedIronkv.Bundle

Per-package implementation bundle for the `VerifiedIronkv` root package.
Collects API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure VerifiedIronkvBundle where
  clone_l151 : Bank.CloneL151Sig
  valid_physical_address : Bank.ValidPhysicalAddressSig
  send : Bank.SendSig
  get_l1102 : Bank.GetL1102Sig
  set_l1115 : Bank.SetL1115Sig
  range_consistent_impl : Bank.RangeConsistentImplSig
  new_l1053 : Bank.NewL1053Sig
  delegate_for_key_range_is_host_impl : Bank.DelegateForKeyRangeIsHostImplSig
  is_message_marshallable : Bank.IsMessageMarshallableSig
  is_marshallable : Bank.IsMarshallableSig
  get : Bank.GetSig
  sht_demarshall_data_method : Bank.ShtDemarshallDataMethodSig
  test_unique : Bank.TestUniqueSig
  endpoints_contain : Bank.EndpointsContainSig
  real_init_impl : Bank.RealInitImplSig
  new_impl : Bank.NewImplSig
  receive_real_packet_impl : Bank.ReceiveRealPacketImplSig
  should_ack_sigle_message_impl : Bank.ShouldAckSigleMessageImplSig
  maybe_ack_packet_impl : Bank.MaybeAckPacketImplSig
  receive_ack_impl : Bank.ReceiveAckImplSig
  send_single_cmessage : Bank.SendSingleCmessageSig
  retransmit_un_acked_packets : Bank.RetransmitUnAckedPacketsSig
  receive_impl : Bank.ReceiveImplSig
