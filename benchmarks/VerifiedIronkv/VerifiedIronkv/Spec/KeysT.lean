import VerifiedIronkv.Harness

/-!
# VerifiedIronkv.Spec.KeysT

Frozen specifications for `KeysT`.

DO NOT MODIFY — curator-given content.
-/

/-- `SHTKey.clone` preserves the exact key value. -/
def spec_clone_l151_preserves_key (impl : RepoImpl) : Prop :=
  ∀ (x : SHTKey), impl.verifiedIronkv.clone_l151 x = x
