-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.Impl.MachineTypes

Machine-word type aliases and size constants for 8/16/32/64-bit unsigned
integers. Translated from `src/BitFields/Spec/MachineTypes.s.dfy`.

All items here are curator-given vocabulary — no implementation slots.
Other modules in this benchmark import this file for the `uint64`, `uint32`,
`uint16`, and `uint8` type aliases.

DO NOT MODIFY types or constants — these are the fixed vocabulary.
-/

-- ── Types (no markers — fixed vocabulary) ──────────────────────────────────

/-- 64-bit unsigned integer (maps to Dafny `uint64` bounded nat). -/
abbrev uint64 := UInt64

/-- 32-bit unsigned integer (maps to Dafny `uint32` bounded nat). -/
abbrev uint32 := UInt32

/-- 16-bit unsigned integer (maps to Dafny `uint16` bounded nat). -/
abbrev uint16 := UInt16

/-- 8-bit unsigned integer (maps to Dafny `uint8` bounded nat). -/
abbrev uint8 := UInt8

-- ── Spec helpers (constants) — no markers ──────────────────────────────────

/-- Maximum value representable in 64 bits. -/
def UINT64_MAX : Nat := 0xffff_ffff_ffff_ffff

/-- Maximum value representable in 32 bits. -/
def UINT32_MAX : Nat := 0xffff_ffff

/-- Maximum value representable in 16 bits. -/
def UINT16_MAX : Nat := 0xffff

/-- Maximum value representable in 8 bits. -/
def UINT8_MAX : Nat := 0xff

/-- Machine word size in bits (64). -/
def WORD_SIZE : Nat := 64
