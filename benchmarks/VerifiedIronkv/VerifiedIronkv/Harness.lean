import VerifiedIronkv.Bundle

/-!
# VerifiedIronkv.Harness

Benchmark harness: `RepoImpl` structure, `canonical` wiring, and the `joint_unsat` macro.

DO NOT MODIFY — benchmark infrastructure.
-/

structure RepoImpl where
  verifiedIronkv : VerifiedIronkvBundle

noncomputable def canonical : RepoImpl where
  verifiedIronkv := {
    clone_l151 := Bank.clone_l151
    valid_physical_address := Bank.valid_physical_address
    send := Bank.send
    get_l1102 := Bank.get_l1102
    set_l1115 := Bank.set_l1115
    range_consistent_impl := Bank.range_consistent_impl
    new_l1053 := Bank.new_l1053
    delegate_for_key_range_is_host_impl := Bank.delegate_for_key_range_is_host_impl
    is_message_marshallable := Bank.is_message_marshallable
    is_marshallable := Bank.is_marshallable
    get := Bank.get
    sht_demarshall_data_method := Bank.sht_demarshall_data_method
    test_unique := Bank.test_unique
    endpoints_contain := Bank.endpoints_contain
    real_init_impl := Bank.real_init_impl
    new_impl := Bank.new_impl
    receive_real_packet_impl := Bank.receive_real_packet_impl
    should_ack_sigle_message_impl := Bank.should_ack_sigle_message_impl
    maybe_ack_packet_impl := Bank.maybe_ack_packet_impl
    receive_ack_impl := Bank.receive_ack_impl
    send_single_cmessage := Bank.send_single_cmessage
    retransmit_un_acked_packets := Bank.retransmit_un_acked_packets
    receive_impl := Bank.receive_impl
  }

/-- `joint_unsat spec_A spec_B [spec_C …] by <proof>` generates the conjunction unsat theorem. -/
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
