import VerifiedBitmasks.Harness
import VerifiedBitmasks.Impl.BitmaskFixedChunks

/-!
# VerifiedBitmasks.Spec.BitmaskFixedChunks

Specifications for the `BitmaskFixedChunks` module. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl` or directly over the chunk
representation types.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Two valid chunk bitmasks are equal iff their flat boolean interpretations are equal. -/
def spec_bFC_IEqual (_impl : RepoImpl) : Prop :=
  ∀ (A B : BFC_T), BFC_Inv A → BFC_Inv B → (A = B ↔ BFC_I A = BFC_I B)
