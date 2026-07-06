-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VestV2.Impl.Utils

Utility type classes (conversion traits, comparison, reflexivity) and
helper functions for the VestV2 parser/serializer framework. The type
classes model Verus's `SpecFrom`/`Into`/`TryFrom`/`TryInto`/`Compare`
traits, and the helper functions provide byte-vector operations used
throughout the combinator implementations.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
Implement only the function bodies.
-/

-- ── Type classes (DO NOT MODIFY) ─────────────────────────────

/-- Spec-level total conversion from T to Self. -/
class SpecFrom (Self T : Type) where
  spec_from : T → Self

/-- Spec-level total conversion from Self to T. -/
class SpecInto (Self T : Type) where
  spec_into : Self → T

/-- Exec-level total conversion from T to Self. -/
class VestFrom (Self T : Type) where
  ex_from : T → Self

/-- Exec-level total conversion from Self to T. -/
class VestInto (Self T : Type) where
  ex_into : Self → T

/-- Spec-level fallible conversion from T to Self. -/
class SpecTryFrom (Self T : Type) (E : outParam Type) where
  spec_try_from : T → Except E Self

/-- Spec-level fallible conversion from Self to T. -/
class SpecTryInto (Self T : Type) (E : outParam Type) where
  spec_try_into : Self → Except E T

/-- Exec-level fallible conversion from T to Self. -/
class VestTryFrom (Self T : Type) (E : outParam Type) where
  ex_try_from : T → Except E Self

/-- Exec-level fallible conversion from Self to T. -/
class VestTryInto (Self T : Type) (E : outParam Type) where
  ex_try_into : Self → Except E T

/-- Trait for comparing two values of potentially different types. -/
class Compare (Self Other : Type) where
  compare : Self → Other → Bool

/-- Trait asserting that view reflexivity holds for a type. -/
class ViewReflex (α : Type) where
  reflex : ∀ (x : α), x = x

namespace VestV2

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

abbrev SetRangeSig := List UInt8 → Nat → List UInt8 → List UInt8
abbrev CompareSliceSig := List UInt8 → List UInt8 → Bool
abbrev InitVecU8Sig := Nat → List UInt8

end VestV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ────────────────────

-- !benchmark @start code_aux def=setRange
-- !benchmark @end code_aux def=setRange

def VestV2.setRange : VestV2.SetRangeSig :=
-- !benchmark @start code def=setRange
  fun data i input =>
    data.take i ++ input ++ data.drop (i + input.length)
-- !benchmark @end code def=setRange

-- !benchmark @start code_aux def=compareSlice
-- !benchmark @end code_aux def=compareSlice

def VestV2.compareSlice : VestV2.CompareSliceSig :=
-- !benchmark @start code def=compareSlice
  fun x y => x == y
-- !benchmark @end code def=compareSlice

-- !benchmark @start code_aux def=initVecU8
-- !benchmark @end code_aux def=initVecU8

def VestV2.initVecU8 : VestV2.InitVecU8Sig :=
-- !benchmark @start code def=initVecU8
  fun n => List.replicate n 0
-- !benchmark @end code def=initVecU8
