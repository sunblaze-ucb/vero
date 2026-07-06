import Bitlist.Impl.Bitlist

/-!
# Bitlist.Bundle

Per-package implementation bundle for the `Bitlist` root package.
Collects all 5 API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

--   name in Lean 4 and cannot be used as a field name. Renamed to `make`.
--   Specs use `impl.bitlist.make`; canonical wires it to `Bitlist.mk`.
structure BitlistBundle where
  make            : Bitlist.MkSig
  length          : Bitlist.LengthSig
  add             : Bitlist.AddSig
  bitlist_getitem : Bitlist.GetitemSig
  bitlistToInt    : Bitlist.ToIntSig
