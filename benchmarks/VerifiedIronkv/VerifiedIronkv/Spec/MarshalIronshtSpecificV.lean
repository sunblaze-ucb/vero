import VerifiedIronkv.Harness

/-!
# VerifiedIronkv.Spec.MarshalIronshtSpecificV

Frozen specifications for `MarshalIronshtSpecificV`.

DO NOT MODIFY — curator-given content.
-/

/-- Source `SHTKey.view_equal_spec`: macro-generated view equality is key equality. -/
def spec_sht_key_view_equal_iff_eq (_impl : RepoImpl) : Prop :=
  ∀ (x y : SHTKey), view_equal x y = true ↔ x = y

/-- Source `EndPoint.view_equal_spec`: macro-generated view equality is equality of abstract endpoint views. -/
def spec_endpoint_view_equal_iff_view (_impl : RepoImpl) : Prop :=
  ∀ (x y : EndPoint), view_equal x y = true ↔ ioTView x = ioTView y
