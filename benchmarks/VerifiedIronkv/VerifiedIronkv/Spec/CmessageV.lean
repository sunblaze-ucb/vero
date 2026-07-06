import VerifiedIronkv.Harness

/-!
# VerifiedIronkv.Spec.CmessageV

Frozen specifications for `CmessageV`.

DO NOT MODIFY — curator-given content.
-/

/-- `is_message_marshallable` returns the selected executable model of the source `message_marshallable` predicate. -/
def spec_is_message_marshallable_matches_model (impl : RepoImpl) : Prop :=
  ∀ (x : CMessage), impl.verifiedIronkv.is_message_marshallable x = messageMarshallableModel x

/-- `is_marshallable` returns the selected executable model of the source `marshallable` predicate. -/
def spec_is_marshallable_matches_model (impl : RepoImpl) : Prop :=
  ∀ (x : CSingleMessage), impl.verifiedIronkv.is_marshallable x = singleMessageMarshallableModel x
