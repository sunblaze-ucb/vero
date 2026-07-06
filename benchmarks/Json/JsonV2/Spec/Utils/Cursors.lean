import JsonV2.Harness

/-!
# Json.Spec.Utils.Cursors

Frozen specifications for cursor arithmetic from `JSON.Utils.Cursors`.

DO NOT MODIFY - this file is frozen curator-given content.
-/

open JSON

/-- The cursor length is the sum of the prefix and suffix lengths. -/
def spec_prefixSuffixLength (impl : RepoImpl) : Prop :=
  ∀ (cs : Cursor_),
    cursor__Valid? cs →
    (cs.end_ - cs.beg).toNat = (cs.point - cs.beg).toNat + (cs.end_ - cs.point).toNat
