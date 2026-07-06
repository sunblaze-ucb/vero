import VerifiedBitmasks.Harness

/-!
# VerifiedBitmasks.Spec.BitmaskSpec

Specifications for the canonical bitmask model. Each `spec_*` is a
mathematical property over the frozen `BitmaskSpec` vocabulary; no API
implementation is required (this module has no Bundle fields).

The `impl` parameter is present for pipeline uniformity but is unused here —
all properties are stated directly over the spec-helper functions.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Population count distributes over concatenation:
    `popcnt(A ++ B) = popcnt(A) + popcnt(B)`. -/
def spec_popcnt_dist (_impl : RepoImpl) : Prop :=
  ∀ (A B : T), bitmask_popcnt (bitmask_concat A B) = bitmask_popcnt A + bitmask_popcnt B

/-- Splitting the concatenation of `A` and `B` at the length of `A` recovers `A` and `B`. -/
def spec_bitmask_split_concat (_impl : RepoImpl) : Prop :=
  ∀ (A B : T), bitmask_split (bitmask_concat A B) (bitmask_nbits A) = (A, B)

/-- A bitmask is all-zeros iff its population count is zero. -/
def spec_bitmask_zeros_popcnt (_impl : RepoImpl) : Prop :=
  ∀ (A : T), bitmask_is_zeros A ↔ bitmask_popcnt A = 0

/-- A bitmask is all-ones iff its population count equals its number of bits. -/
def spec_bitmask_ones_popcnt (_impl : RepoImpl) : Prop :=
  ∀ (A : T), bitmask_is_ones A ↔ bitmask_popcnt A = bitmask_nbits A
