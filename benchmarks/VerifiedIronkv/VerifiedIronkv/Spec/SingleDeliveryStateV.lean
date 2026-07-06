import VerifiedIronkv.Harness

/-!
# VerifiedIronkv.Spec.SingleDeliveryStateV

Frozen specifications for `SingleDeliveryStateV`.

DO NOT MODIFY — curator-given content.
-/

/-- The scored send-state lookup API matches any source ghost lookup represented by the endpoint map entries. -/
def spec_get_matches_hashmap_lookup (impl : RepoImpl) : Prop :=
  ∀ (sendState : CSendState) (dst : EndPoint)
      (ghostLookup : AbstractEndPoint → Option CAckState),
    endpointHashmapEntriesRepresentMap sendState.epmap.entries ghostLookup →
    impl.verifiedIronkv.get sendState dst =
      ghostLookup (ioTView dst)
