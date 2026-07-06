/-!
# VestV2.Impl.RegularLeb128Unrolled

Unrolled unsigned LEB128 variant. This module defines the
`UnsignedLEB128Unrolled` combinator type, a compile-time-unrolled
version of the LEB128 encoder/decoder for performance.

Types are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────

/-- The unrolled unsigned LEB128 combinator (unit-like). -/
structure UnsignedLEB128Unrolled where
  deriving Inhabited
