import Flocq.Harness
import Flocq.IEEE754.Impl.PrimFloat

/-!
# Flocq.IEEE754.Spec.PrimFloat

Specifications for the Flocq ↔ native-float conversion functions.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

These specs correspond to Coq's `B2Prim_Prim2B` and `Prim2B_B2Prim` from
`src/IEEE754/PrimFloat.v`: the two conversion functions form a round-trip
isomorphism on well-formed IEEE 754 binary64 values.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- B2Prim after Prim2B is the identity on native floats.

    Corresponds to `B2Prim_Prim2B` in the Coq source: for any native
    `Float x`, converting it to a `BinaryFloat 53 1024` via `prim2B` and
    back to a `Float` via `b2Prim` recovers `x` exactly. -/
def spec_B2Prim_Prim2B (impl : RepoImpl) : Prop :=
  ∀ (x : Float), impl.flocq.b2Prim (impl.flocq.prim2B x) = x

/-- Prim2B after B2Prim is the identity on binary64 floats.

    Corresponds to `Prim2B_B2Prim` in the Coq source: for any well-formed
    `BinaryFloat 53 1024` value `x`, converting it to a native `Float` via
    `b2Prim` and back via `prim2B` recovers `x` exactly. -/
def spec_Prim2B_B2Prim (impl : RepoImpl) : Prop :=
  ∀ (x : BinaryFloat 53 1024), impl.flocq.prim2B (impl.flocq.b2Prim x) = x
