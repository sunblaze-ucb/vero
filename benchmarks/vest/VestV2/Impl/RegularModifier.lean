import VestV2.Impl.Properties

/-!
# VestV2.Impl.RegularModifier

Modifier combinators for the VestV2 parser/serializer framework.
Defines isomorphisms (total and partial), predicates, and structural
combinators (Mapped, TryMap, Refined, Cond, AndThen) that transform
or constrain inner combinators.

Types are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────

/-- Spec-level total isomorphism between `Src` and `Dst`,
    parameterized by a phantom type `Self`. -/
class SpecIso (Self Src Dst : Type) where
  spec_iso : Src → Dst
  spec_iso_rev : Dst → Src

/-- Function bundle for a spec-level total isomorphism. -/
structure SpecIsoFn (Src Dst : Type) where
  spec_iso : Src → Dst
  spec_iso_rev : Dst → Src

/-- Proof obligations for a spec-level total isomorphism:
    both directions are roundtrip-correct. -/
class SpecIsoProof (Self Src Dst : Type) [inst : SpecIso Self Src Dst] where
  spec_iso_ok : ∀ (s : Src), inst.spec_iso_rev (inst.spec_iso s) = s
  spec_iso_rev_ok : ∀ (d : Dst), inst.spec_iso (inst.spec_iso_rev d) = d

/-- Exec-level total isomorphism between `Src` and `Dst`. -/
class Iso (Self Src Dst : Type) where
  ex_iso : Src → Dst
  ex_iso_rev : Dst → Src

/-- Function bundle for an exec-level total isomorphism. -/
structure IsoFn (Src Dst : Type) where
  ex_iso : Src → Dst
  ex_iso_rev : Dst → Src

/-- Spec-level partial (fallible) isomorphism between `Src` and `Dst`. -/
class SpecPartialIso (Self Src Dst : Type) where
  spec_iso : Src → Option Dst
  spec_iso_rev : Dst → Src

/-- Function bundle for a spec-level partial isomorphism. -/
structure SpecPartialIsoFn (Src Dst : Type) where
  spec_iso : Src → Option Dst
  spec_iso_rev : Dst → Src

/-- Proof obligation for a spec-level partial isomorphism:
    the reverse direction always succeeds. -/
class SpecPartialIsoProof (Self Src Dst : Type) [inst : SpecPartialIso Self Src Dst] where
  spec_iso_rev_ok : ∀ (d : Dst), inst.spec_iso (inst.spec_iso_rev d) = some d

/-- Exec-level partial (fallible) isomorphism between `Src` and `Dst`. -/
class PartialIso (Self Src Dst : Type) where
  ex_iso : Src → Option Dst
  ex_iso_rev : Dst → Src

/-- Function bundle for an exec-level partial isomorphism. -/
structure PartialIsoFn (Src Dst : Type) where
  ex_iso : Src → Option Dst
  ex_iso_rev : Dst → Src

/-- Spec-level predicate over type `T`, parameterized by a phantom `Self`. -/
class SpecPred (Self T : Type) where
  spec_pred : Self → T → Bool

/-- Exec-level predicate over type `T`. -/
class Pred (Self T : Type) [SpecPred Self T] where
  pred : T → Bool

/-- Combinator that maps the result of an `inner` combinator with a
    total isomorphism. -/
structure Mapped (Inner Mapper : Type) where
  inner : Inner
  mapper : Mapper

/-- Combinator that maps the result of an `inner` combinator with a
    fallible (partial) isomorphism. -/
structure TryMap (Inner Mapper : Type) where
  inner : Inner
  mapper : Mapper

/-- Combinator that refines the result of an `inner` combinator with
    a predicate. -/
structure Refined (Inner Predicate : Type) where
  inner : Inner
  predicate : Predicate

/-- Combinator that conditionally delegates to the `inner` combinator
    based on a boolean flag. -/
structure Cond (Inner : Type) where
  cond : Bool
  inner : Inner

namespace VestV2

/-- Combinator that monadically chains two combinators. -/
structure AndThen (Fst Snd : Type) where
  fst : Fst
  snd : Snd

end VestV2

-- ── Spec helpers (no markers — fixed vocabulary) ──────────

/-- Mapped combinator's spec_parse: parses with the inner combinator
    and maps the result through the isomorphism. -/
def Mapped.spec_parse {Inner Src Dst M : Type} [SpecCombinator Inner Src] [SpecIso M Src Dst]
    (c : Mapped Inner M) (s : List UInt8) : Option (Int × Dst) :=
  match SpecCombinator.spec_parse c.inner s with
  | some (n, v) => some (n, SpecIso.spec_iso (Self := M) v)
  | none => none
