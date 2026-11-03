# WORKLOG

## 2026-11-02

- Replaced the FLoCq decoder/validity axioms with concrete IEEE semantics, corrected unsigned sign/exponent extraction and the native minimum-normal encoding bug, and restored source format/value invariants (#3). All 203 scored specification names remain; the trusted inventory is now 11 declarations. Native conversion restores the source single-NaN domain and exposes platform laws as explicit premises, with no new global axiom. The locked Lean C runtime confirms NaN canonicalization.
- Full `lake build` and runtime boundary regressions pass. Five curator kernel regressions assert only standard axiom dependencies; generated Bits/PrimFloat proof modules compile in both modes. The 81 Python validation/materialization tests, Ruff, specification/trust checks, and whitespace checks pass. Historical artifact scores require fresh evaluation; no grader timeout changes.

## 2026-10-28

- Reconnected the twelve FLoCq arithmetic wrappers to their existing namespaced operations and removed the six redundant trusted declarations (#3). Restored the bit-roundtrip range premise from the source. `lake build Flocq.Test` passes, including twelve definitional wrapper regressions. Native-Float inverse laws and the decoder/validity boundary remain curator work.
