import VerifiedIronkv.Harness

/-!
# VerifiedIronkv.Spec.HostImplV

Frozen specifications for `HostImplV`.

DO NOT MODIFY — curator-given content.
-/

/-- `real_init_impl` returns a host state satisfying the selected initialization ensures model. -/
def spec_real_init_impl_satisfies_init_ensures (impl : RepoImpl) : Prop :=
  ∀ (netc : NetClient) (args : Args), netClientValidModel netc →
    hostInitEnsuresModel netc args (impl.verifiedIronkv.real_init_impl netc args) ∧
    hostInitEnsuresSourceBridge netc args (impl.verifiedIronkv.real_init_impl netc args)
