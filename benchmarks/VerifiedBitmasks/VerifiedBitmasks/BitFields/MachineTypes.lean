-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.BitFields.MachineTypes

Machine-word type aliases and size constants for 8/16/32/64-bit unsigned
integers.  All items here are curator-given vocabulary — no implementation
slots.

DO NOT MODIFY types or constants — these are the fixed vocabulary.
-/

-- ── Types (no markers — fixed vocabulary) ──────────────────────────────────

/-- 64-bit unsigned integer (maps to Dafny `uint64` / `bv64` bounded nat). -/
abbrev uint64 := UInt64

/-- 32-bit unsigned integer. -/
abbrev uint32 := UInt32

/-- 16-bit unsigned integer. -/
abbrev uint16 := UInt16

/-- 8-bit unsigned integer. -/
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
