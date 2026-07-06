import VestV2.Impl.RegularDisjoint
import VestV2.Harness

/-!
# VestV2.Spec.RegularDisjoint

Specifications for the disjointness trait. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- If two combinators are disjoint, they cannot both successfully
    parse the same buffer: at most one parse can succeed. -/
def spec_disjoint_from_parse_exclusion (_impl : RepoImpl) : Prop :=
  ∀ (Self Other A B : Type) [SpecCombinator Self A] [SpecCombinator Other B]
    [_inst : DisjointFrom Self Other] (s : Self) (o : Other) (buf : List UInt8),
  DisjointFrom.disjoint_from s o = true →
  ¬(SpecCombinator.spec_parse s buf ≠ none ∧ SpecCombinator.spec_parse o buf ≠ none)
