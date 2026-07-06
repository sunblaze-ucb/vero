import VerifiedIronkv.Impl.SeqIsUniqueV
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedIronkv.Impl.HostImplV

Translated Verus vocabulary and reference implementations for `HostImplV`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

structure Parameters where
  max_seqno : Nat
  max_delegations : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

structure Constants where
  root_identity : EndPoint
  host_ids : List EndPoint
  params : Parameters
  me : EndPoint
  deriving Repr, DecidableEq, BEq, Inhabited

structure HostState where
  next_action_index : Nat
  resend_count : Nat
  constants : Constants
  delegation_map : DelegationMap CKey
  h : CKeyHashMap
  sd : CSingleDelivery
  received_packet : Option CPacket
  num_delegations : Nat
  received_requests : List AppRequest
  deriving Repr, DecidableEq, BEq, Inhabited

def endpointsFromArgs (args : Args) : List EndPoint :=
  args.map (fun arg => { id := arg })

def staticParametersModel : Parameters :=
  { max_seqno := 18446744073709551615, max_delegations := 9223372036854775807 }

def endpointValidPhysicalAddressModel (ep : EndPoint) : Prop :=
  ep.id.length < 1048576

def netClientOkModel (netc : NetClient) : Prop :=
  netc.state ≠ State.Error

def netClientValidModel (netc : NetClient) : Prop :=
  netc.state ≠ State.Error ∧ endpointValidPhysicalAddressModel netc.end_point

def cKeyHashMapEmptyViewBridge (h : CKeyHashMap) : Prop :=
  h.m = []

def cSingleDeliveryEmptyInitBridge (sd : CSingleDelivery) : Prop :=
  sd.receive_state.epmap.entries = [] ∧
  sd.send_state.epmap.entries = []

def hostParsedConfigurationBridge (args : Args) (me : EndPoint) (rc : Option Constants) : Prop :=
  let hostIds := endpointsFromArgs args
  match hostIds with
  | [] => rc = none
  | root :: _ =>
      if hostIds.all Bank.valid_physical_address && Bank.test_unique hostIds then
        rc = some {
          root_identity := root,
          host_ids := hostIds,
          params := staticParametersModel,
          me := me
        }
      else rc = none

def hostInitEnsuresModel (netc : NetClient) (args : Args) (rc : Option HostState) : Prop :=
  let hostIds := endpointsFromArgs args
  match hostIds with
  | [] => rc = none
  | root :: _ =>
      if hostIds.all Bank.valid_physical_address && Bank.test_unique hostIds then
        match rc with
        | some hs =>
            netClientValidModel netc ∧
          hostParsedConfigurationBridge args netc.end_point (some hs.constants) ∧
          hs.next_action_index = 0 ∧
          hs.resend_count = 0 ∧
          (endpointsFromArgs args).all Bank.valid_physical_address = true ∧
          Bank.test_unique (endpointsFromArgs args) = true ∧
          delegationMapValid hs.delegation_map = true ∧
          hs.constants.root_identity = root ∧
          hs.constants.host_ids = endpointsFromArgs args ∧
          hs.constants.params = staticParametersModel ∧
          hs.constants.me = netc.end_point ∧
          ioTView hs.constants.me = ioTView netc.end_point ∧
          hs.delegation_map = Bank.new_l1053 { ukey := 0 } root ∧
          cKeyHashMapEmptyViewBridge hs.h ∧
          hs.h = { m := [] } ∧
          cSingleDeliveryEmptyInitBridge hs.sd ∧
          hs.sd = { receive_state := { epmap := { entries := [] } }, send_state := { epmap := { entries := [] } } } ∧
          hs.received_packet = none ∧
          hs.num_delegations = 1 ∧
          hs.received_requests = []
        | none => False
      else rc = none

def hostStateInitInvariantBridge (hs : HostState) (netcEndPoint : AbstractEndPoint) : Prop :=
  hs.next_action_index < 3 ∧
  delegationMapValid hs.delegation_map = true ∧
  ioTView hs.constants.me = netcEndPoint ∧
  abstractEndPointValid (ioTView hs.constants.me) = true ∧
  Bank.test_unique hs.constants.host_ids = true ∧
  abstractEndPointValid (ioTView hs.constants.root_identity) = true ∧
  valid_L337 hs.sd = true ∧
  hs.num_delegations < hs.constants.params.max_delegations ∧
  hs.constants.params = staticParametersModel ∧
  hs.resend_count < 100000000

def hostProtocolInitConcreteBridge
    (hs : HostState) (netc : NetClient) (args : Args)
    (delegationGhost : CKey → AbstractEndPoint) : Prop :=
  let hostIds := endpointsFromArgs args
  match hostIds with
  | [] => False
  | root :: _ =>
      hostIds.all Bank.valid_physical_address = true ∧
      hs.constants.root_identity = root ∧
      hs.constants.host_ids = hostIds ∧
      hs.constants.params = staticParametersModel ∧
      hs.constants.me = netc.end_point ∧
      delegationMapNewTotalDefault hs.delegation_map root ∧
      delegationMapGhostTotalViewBridge hs.delegation_map delegationGhost ∧
      (∀ k : CKey, delegationGhost k = ioTView root) ∧
      cKeyHashMapEmptyViewBridge hs.h ∧
      hs.h = { m := [] } ∧
      cSingleDeliveryEmptyInitBridge hs.sd ∧
      hs.sd = { receive_state := { epmap := { entries := [] } }, send_state := { epmap := { entries := [] } } } ∧
      hs.received_packet = none ∧
      hs.num_delegations = 1 ∧
      hs.received_requests = []

def hostInitEnsuresSourceBridge (netc : NetClient) (args : Args) (rc : Option HostState) : Prop :=
  match rc with
  | none => True
  | some hs =>
      netClientOkModel netc ∧
      hostParsedConfigurationBridge args netc.end_point (some hs.constants) ∧
      hostStateInitInvariantBridge hs (ioTView netc.end_point) ∧
      ∃ delegationGhost, hostProtocolInitConcreteBridge hs netc args delegationGhost

namespace Bank

abbrev RealInitImplSig := NetClient → Args → Option HostState

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=real_init_impl
-- !benchmark @end code_aux def=real_init_impl

def Bank.real_init_impl : Bank.RealInitImplSig :=
-- !benchmark @start code def=real_init_impl
  fun netc args =>
    let hostIds := endpointsFromArgs args
    match hostIds with
    | [] => none
    | root :: _ =>
        if hostIds.all Bank.valid_physical_address && Bank.test_unique hostIds then
          some {
            next_action_index := 0,
            resend_count := 0,
            constants := {
              root_identity := root,
              host_ids := hostIds,
              params := staticParametersModel,
              me := netc.end_point
            },
            delegation_map := Bank.new_l1053 { ukey := 0 } root,
            h := { m := [] },
            sd := { receive_state := { epmap := { entries := [] } }, send_state := { epmap := { entries := [] } } },
            received_packet := none,
            num_delegations := 1,
            received_requests := []
          }
        else none
-- !benchmark @end code def=real_init_impl
