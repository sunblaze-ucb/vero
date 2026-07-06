import JsonV2.Harness

/-!
# Json.Spec.ConcreteSyntax.Spec

Frozen specifications for concrete-syntax serialization vocabulary from
`JSON.ConcreteSyntax.Spec`.
-/

open JSON

/-- Value serialization unfolds to number serialization for number grammar values. -/
def spec_unfoldValueNumber (impl : RepoImpl) : Prop :=
  ∀ (n : GrammarNumber), csValue (.number n) = csNumber n

/-- Value serialization unfolds to object serialization for object grammar values. -/
def spec_unfoldValueObject (impl : RepoImpl) : Prop :=
  ∀ (obj : CSObject), csValue (.object obj) = csObject obj

/-- Value serialization unfolds to array serialization for array grammar values. -/
def spec_unfoldValueArray (impl : RepoImpl) : Prop :=
  ∀ (arr : CSArray), csValue (.array arr) = csArray arr
