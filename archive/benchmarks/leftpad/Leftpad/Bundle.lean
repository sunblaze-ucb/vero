import Leftpad.Impl.Leftpad

/-!
# Leftpad.Bundle

Per-package implementation bundle for the leftpad benchmark.
-/

structure LeftpadBundle where
  leftpad       : Leftpad.LeftpadSig
  leftpadString : Leftpad.LeftpadStringSig
