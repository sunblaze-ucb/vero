import VerifiedIronkv.Harness

/-!
# VerifiedIronkv.Spec.NetShtV

Frozen specifications for `NetShtV`.

DO NOT MODIFY — curator-given content.
-/

/-- Demarshalling accepted bytes consumes exactly a source-shaped serialized single message and satisfies the endpoint checks performed by `sht_demarshall_data_method`. -/
def spec_sht_demarshall_data_method_returns_marshalable (impl : RepoImpl) : Prop :=
  ∀ (data : List Nat),
    match parseCSingleMessage data 0 with
    | some (msg, count) =>
      if decide (count = data.length) && acceptedEndpointChecks msg && wireMarshalableCSingleMessage msg && cSingleMessageGeneratedWireMarshalableModel msg && cSingleMessageAbstractableModel msg then
        impl.verifiedIronkv.sht_demarshall_data_method data = msg
        else
          impl.verifiedIronkv.sht_demarshall_data_method data = CSingleMessage.InvalidMessage
    | none => impl.verifiedIronkv.sht_demarshall_data_method data = CSingleMessage.InvalidMessage
