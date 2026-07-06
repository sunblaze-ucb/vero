import PiggybankV2.Harness

/-!
# PiggybankV2.Spec.PiggyBank

Spec-side PiggyBank helpers that depend on an arbitrary implementation
bundle.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

/-- Assemble the weak ConCert contract from an implementation bundle's entrypoints. -/
noncomputable def contract (impl : RepoImpl) : Contract Setup Msg State Error :=
  build_contract impl.piggybankV2.init impl.piggybankV2.receive
