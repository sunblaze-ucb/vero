import VestV2.Harness

/-!
# VestV2.Spec.RegularClone

Specifications for clone operations. Each clone implementation must be
reflexive: the cloned value equals the original.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- All clone implementations are reflexive: the cloned value equals the original. -/
def spec_clone_reflexive (impl : RepoImpl) : Prop :=
  (∀ (x : U8), impl.vest.cloneU8 x = x) ∧
  (∀ (x : U16Le), impl.vest.cloneU16Le x = x) ∧
  (∀ (x : U32Le), impl.vest.cloneU32Le x = x) ∧
  (∀ (x : U64Le), impl.vest.cloneU64Le x = x) ∧
  (∀ (x : Tail), impl.vest.cloneTail x = x) ∧
  (∀ (x : Variable), impl.vest.cloneVariable x = x) ∧
  (∀ (x : Fixed), impl.vest.cloneFixed x = x)
