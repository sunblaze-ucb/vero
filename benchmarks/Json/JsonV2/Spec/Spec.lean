import JsonV2.Harness

/-!
# Json.Spec.Spec

Frozen specifications for serialization support from `JSON.Spec`.
-/

/-- Integer decimal rendering emits only ASCII bytes. -/
def spec_ofIntOnlyASCII (impl : RepoImpl) : Prop :=
  ∀ (n : Int), ∀ c ∈ (impl.json.intToBytes n), c.toNat < 128
