import JsonPatch.Impl.Pointer
import JsonPatch.Impl.Patch

/-!
# JsonPatch.Bundle

Per-package implementation bundle for the `JsonPatch` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure JsonPatchBundle where
  escape   : JsonPatch.EscapeSig
  unescape : JsonPatch.UnescapeSig
  resolve  : JsonPatch.ResolveSig
  applyOp  : JsonPatch.ApplyOpSig
  apply    : JsonPatch.ApplySig
