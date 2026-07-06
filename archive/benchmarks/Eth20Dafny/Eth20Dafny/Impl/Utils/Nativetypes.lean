-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eth20Dafny.Impl.Utils.Nativetypes

Fixed native numeric type aliases translated from `utils/NativeTypes.dfy`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
-/


-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Eth20Dafny

abbrev sbyte := Int
abbrev int16 := Int
abbrev uint16 := UInt16
abbrev int32 := Int
abbrev int64 := Int
abbrev nat8 := Fin 128
abbrev nat16 := Fin 32768
abbrev nat32 := Fin 2147483648
abbrev nat64 := Fin 9223372036854775808
abbrev uint8 := UInt8
abbrev uint32 := UInt32
abbrev uint64 := UInt64

end Eth20Dafny
