import VerifiedIronkv.Harness

/-!
# VerifiedIronkv.Spec.IoT

Frozen specifications for `IoT`.

DO NOT MODIFY — curator-given content.
-/

/-- `send` preserves the endpoint and updates state/history according to the trusted callback result. -/
def spec_io_send_updates_state_history_over_trusted_callback (impl : RepoImpl) : Prop :=
  ∀ (netc : NetClient) (recipient : EndPoint) (message : List Nat), netc.state ≠ State.Error →
    let trusted := Bank.send_internal_wrapper netc recipient message
    let out := impl.verifiedIronkv.send netc recipient message
    out.2 = trusted.2 ∧ ioSendTrustedCallbackModel netc out.1 recipient message trusted.2

/-- Physical-address validity follows the source endpoint byte-length bound. -/
def spec_valid_physical_address_matches_length_bound (impl : RepoImpl) : Prop :=
  ∀ (x : EndPoint), impl.verifiedIronkv.valid_physical_address x = decide (x.id.length < 1048576)
