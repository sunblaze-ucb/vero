import DafnyVMC.Impl.Rand

/-!
# DafnyVMC.Spec.Rand

Specifications for the Rand module foundations.  The `Bitstream` type,
`prob` measure, and `instMeasurableSpaceBitstream` instance are vocabulary
shared across all DafnyVMC modules; they live in `Impl/Rand.lean` and are
re-exported transitively through this import.

No `spec_*` entries are required for this module — all Rand-level
properties (`probIsProbabilityMeasure`) are axiomatised directly in
`Impl/Rand.lean`.

DO NOT MODIFY — this file is frozen curator-given content.
-/
