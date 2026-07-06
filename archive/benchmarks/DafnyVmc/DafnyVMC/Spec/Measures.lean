import DafnyVMC.Impl.Measures

/-!
# DafnyVMC.Spec.Measures

Specifications for the Measures vocabulary module.

`IsMeasurePreserving`, `AreIndepEvents`, and `PreImage` are pure
vocabulary aliases for Mathlib definitions; they carry no standalone
benchmark specs at the DafnyVMC level.  They are imported transitively
by other spec modules (e.g. `Spec/Independence`) that reference these
measure-theoretic concepts.

DO NOT MODIFY — this file is frozen curator-given content.
-/
