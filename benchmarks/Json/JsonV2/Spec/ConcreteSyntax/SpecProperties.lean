import JsonV2.Harness

/-!
# Json.Spec.ConcreteSyntax.SpecProperties

Frozen specifications for concrete-syntax property vocabulary from
`JSON.ConcreteSyntax.SpecProperties`.
-/

open JSON

/-- Bracketed serialization respects matching structural and element bytes. -/
def spec_bracketed_Morphism (impl : RepoImpl) : Prop :=
  ∀ {L D S R L' D' S' R' : Type}
    (fl : L → List UInt8) (fl' : L' → List UInt8)
    (fd : D → List UInt8) (fd' : D' → List UInt8)
    (fs : S → List UInt8) (fs' : S' → List UInt8)
    (fr : R → List UInt8) (fr' : R' → List UInt8)
    (b : Bracketed L D S R) (b' : Bracketed L' D' S' R'),
    view__Bytes b.l.before = view__Bytes b'.l.before →
    view__Bytes b.r.after = view__Bytes b'.r.after →
    bracketed_Morphism_Requires fl fl' fd fd' fs fs' fr fr' b b' →
    JSON.csBracketed fl fd fs fr b = JSON.csBracketed fl' fd' fs' fr' b'

/-- Concatenating byte chunks respects pointwise equal chunk lists. -/
def spec_concatBytes_Morphism (impl : RepoImpl) : Prop :=
  ∀ (bss bss' : List (List UInt8)),
    bss.length = bss'.length →
    (∀ i, ∀ h : i < bss.length, ∀ h' : i < bss'.length,
      bss.get ⟨i, h⟩ = bss'.get ⟨i, h'⟩) →
    JSON.csConcatBytes bss = JSON.csConcatBytes bss'

/-- Byte-chunk concatenation distributes over list append. -/
def spec_concatBytes_Linear (impl : RepoImpl) : Prop :=
  ∀ (bss1 bss2 : List (List UInt8)),
    JSON.csConcatBytes (bss1 ++ bss2) =
      JSON.csConcatBytes bss1 ++ JSON.csConcatBytes bss2
