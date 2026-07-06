-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Leftpad.Impl.Leftpad

Reference implementations for the list and string leftpad APIs.
-/

namespace Leftpad

abbrev LeftpadSig := {α : Type} → Nat → α → List α → List α
abbrev LeftpadStringSig := Nat → Char → String → String

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=leftpad
-- !benchmark @end code_aux def=leftpad

def leftpad : LeftpadSig :=
-- !benchmark @start code def=leftpad
  fun n a l => List.replicate (n - l.length) a ++ l
-- !benchmark @end code def=leftpad

-- !benchmark @start code_aux def=leftpadString
-- !benchmark @end code_aux def=leftpadString

def leftpadString : LeftpadStringSig :=
-- !benchmark @start code def=leftpadString
  fun n a s => "".pushn a (n - s.length) ++ s
-- !benchmark @end code def=leftpadString

end Leftpad
