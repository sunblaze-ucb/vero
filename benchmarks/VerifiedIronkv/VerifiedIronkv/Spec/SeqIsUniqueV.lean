import VerifiedIronkv.Harness

/-!
# VerifiedIronkv.Spec.SeqIsUniqueV

Frozen specifications for `SeqIsUniqueV`.

DO NOT MODIFY — curator-given content.
-/

/-- Endpoint-list helpers match the source abstract-view uniqueness and membership postconditions. -/
def spec_endpoint_sequence_helpers_match_views (impl : RepoImpl) : Prop :=
  (∀ endpoints : List EndPoint,
    impl.verifiedIronkv.test_unique endpoints =
      decide (List.Nodup (endpoints.map ioTView))) ∧
  (∀ (endpoints : List EndPoint) (endpoint : EndPoint),
    impl.verifiedIronkv.endpoints_contain endpoints endpoint =
      endpoints.any (fun e => ioTView e == ioTView endpoint))
