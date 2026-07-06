import JsonV2.Harness

/-!
# Json.Spec.Utils.Views

Frozen specifications for byte-view copy behavior from
`JSON.Utils.Views.Core`.
-/

open JSON

/-- CopyTo writes the view bytes into the requested destination slice. -/
def spec_view_copy_to_region (impl : RepoImpl) : Prop :=
  ∀ (v : View_) (dest : List UInt8) (start : UInt32),
    view__Valid? v = true →
    start.toNat + (view__Length v).toNat ≤ dest.length →
    start.toNat + (view__Length v).toNat < UInt32.size →
    ((impl.json.view__CopyTo v dest start).drop start.toNat).take (view__Length v).toNat = view__Bytes v

/-- CopyTo preserves the destination suffix after the copied view range. -/
def spec_view_copy_to_suffix_preserved (impl : RepoImpl) : Prop :=
  ∀ (v : View_) (dest : List UInt8) (start : UInt32),
    view__Valid? v = true →
    start.toNat + (view__Length v).toNat ≤ dest.length →
    start.toNat + (view__Length v).toNat < UInt32.size →
    (impl.json.view__CopyTo v dest start).drop (start.toNat + (view__Length v).toNat) =
      dest.drop (start.toNat + (view__Length v).toNat)
