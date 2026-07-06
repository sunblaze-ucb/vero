import Bidict.Harness

/-!
# Bidict.Spec.OnDup

Specifications for the on-duplication action vocabulary (`OnDupAction` and
`OnDup`). Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

These specs do not depend on any `impl` field — they pin down the constructor
distinctness (so that the three actions cannot collapse) and the structural
projections of `OnDup.mk`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- `OnDupAction.raise` is distinct from both `dropOld` and `dropNew`. -/
def spec_OnDupAction_raise_distinct (_impl : RepoImpl) : Prop :=
  OnDupAction.raise ≠ OnDupAction.dropOld ∧
  OnDupAction.raise ≠ OnDupAction.dropNew

/-- `OnDupAction.dropOld` is distinct from both `raise` and `dropNew`. -/
def spec_OnDupAction_dropOld_distinct (_impl : RepoImpl) : Prop :=
  OnDupAction.dropOld ≠ OnDupAction.raise ∧
  OnDupAction.dropOld ≠ OnDupAction.dropNew

/-- `OnDupAction.dropNew` is distinct from both `raise` and `dropOld`. -/
def spec_OnDupAction_dropNew_distinct (_impl : RepoImpl) : Prop :=
  OnDupAction.dropNew ≠ OnDupAction.raise ∧
  OnDupAction.dropNew ≠ OnDupAction.dropOld

/-- `OnDup.mk` is the inverse of its projections: building an `OnDup` and
    reading back its `key` and `val` fields recovers the supplied actions. -/
def spec_OnDup_mk_projections (_impl : RepoImpl) : Prop :=
  ∀ (keyAction valueAction : OnDupAction),
    (OnDup.mk keyAction valueAction).key = keyAction ∧
    (OnDup.mk keyAction valueAction).val = valueAction
