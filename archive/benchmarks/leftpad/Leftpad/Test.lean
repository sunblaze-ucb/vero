import Leftpad.Impl.Leftpad

/-!
# Leftpad.Test

Executable conformance tests for the reference implementations.
-/

#guard Leftpad.leftpad 5 'b' (String.toList "ac") == String.toList "bbbac"
#guard Leftpad.leftpad 2 'b' (String.toList "ac") == String.toList "ac"
#guard Leftpad.leftpad 0 (0 : Nat) [1, 2, 3] == [1, 2, 3]

#guard Leftpad.leftpadString 5 'b' "ac" == "bbbac"
#guard Leftpad.leftpadString 2 'b' "ac" == "ac"
#guard Leftpad.leftpadString 0 'b' "ac" == "ac"
