import VestV2.Impl.RegularModifier
import VestV2.Harness

/-!
# VestV2.Spec.RegularModifier

Specifications for modifier combinators. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- A well-formed Iso satisfies spec_iso (spec_iso_rev d) = d and
    spec_iso_rev (spec_iso s) = s. -/
def spec_iso_roundtrip (_impl : RepoImpl) : Prop :=
  ∀ (Self Src Dst : Type) [inst : SpecIso Self Src Dst] [SpecIsoProof Self Src Dst]
    (s : Src) (d : Dst),
    inst.spec_iso (inst.spec_iso_rev d) = d ∧
    inst.spec_iso_rev (inst.spec_iso s) = s

/-- Mapped combinator is roundtrip correct: if the inner combinator is
    roundtrip correct and the mapper is an iso, then Mapped is roundtrip
    correct. -/
def spec_mapped_roundtrip (_impl : RepoImpl) : Prop :=
  ∀ (Inner Src Dst M : Type) [SpecCombinator Inner Src] [isoInst : SpecIso M Src Dst]
    [SpecIsoProof M Src Dst] (c : Mapped Inner M) (d : Dst),
    Mapped.spec_parse (Dst := Dst) c (SpecCombinator.spec_serialize c.inner (isoInst.spec_iso_rev d)) =
      match SpecCombinator.spec_parse c.inner (SpecCombinator.spec_serialize c.inner (isoInst.spec_iso_rev d)) with
      | none => none
      | some (n, v) => some (n, isoInst.spec_iso v)
