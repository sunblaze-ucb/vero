import JsonV2.Impl.Grammar
import JsonV2.Impl.Utils.Views
import JsonV2.Impl.ConcreteSyntax.Spec

/-!
# Json.Impl.ConcreteSyntax.SpecProperties

Concrete-syntax property vocabulary translated from
`JSON.ConcreteSyntax.SpecProperties`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
-/

namespace JSON

-- Spec helpers (no markers - fixed vocabulary)

def bracketed_Morphism_Requires {L D S R L' D' S' R' : Type}
    (fl : L → List UInt8) (fl' : L' → List UInt8)
    (fd : D → List UInt8) (fd' : D' → List UInt8)
    (fs : S → List UInt8) (fs' : S' → List UInt8)
    (fr : R → List UInt8) (fr' : R' → List UInt8)
    (b : Bracketed L D S R) (b' : Bracketed L' D' S' R') : Prop :=
  fl b.l.t = fl' b'.l.t ∧
    view__Bytes b.l.after = view__Bytes b'.l.after ∧
    view__Bytes b.r.before = view__Bytes b'.r.before ∧
    fr b.r.t = fr' b'.r.t ∧
    b.data.length = b'.data.length ∧
    ∀ (i : Nat) (h : i < b.data.length) (h' : i < b'.data.length),
      csSuffixed fd fs (b.data.get ⟨i, h⟩) =
        csSuffixed fd' fs' (b'.data.get ⟨i, h'⟩)

def csConcatBytes (bss : List (List UInt8)) : List UInt8 :=
  bss.foldl (· ++ ·) []

def csBracketed {L D S R : Type}
    (fl : L → List UInt8) (fd : D → List UInt8)
    (fs : S → List UInt8) (fr : R → List UInt8)
    (b : Bracketed L D S R) : List UInt8 :=
  csStructural fl b.l ++
    csConcatBytes (b.data.map (csSuffixed fd fs)) ++
    csStructural fr b.r

end JSON
