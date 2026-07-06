import JsonPatch.Impl.Pointer
import JsonPatch.Impl.Patch
import JsonPatch.Bundle
import JsonPatch.Harness
import JsonPatch.Spec.Pointer
import JsonPatch.Spec.Patch
import JsonPatch.Test

/-!
# JsonPatch

Root import hub: RFC 6901 JSON Pointer resolution and RFC 6902 JSON Patch
application, ported from the `jsonpointer` (v3.0.0) and `jsonpatch` (v1.33)
libraries (stefankoegl, Modified BSD). JSON is modelled mathlib-free as an
inductive `Json` with an association-list object representation.

Pointer core (`Impl/Pointer`, `Spec/Pointer`): `escape` / `unescape` (the
asymmetric RFC6901 `~0`/`~1` token escaping) and `resolve` (the reference-token
walk). The crown pointer law is the escape/unescape round-trip.

Patch core (`Impl/Patch`, `Spec/Patch`): `applyOp` (one operation) and `apply`
(an operation list, folded with monadic short-circuit). The crown patch
properties are the per-op structural laws (add inserts, remove deletes, replace
overwrites, test is identity-or-fail), the move-vs-copy distinguishing laws
(move = remove-then-add; copy preserves the source), and the op-list composition
homomorphism `apply (p₁ ++ p₂) = apply p₁ >=> apply p₂`.

Behaviour is pinned by `Spec/Pointer.lean` and `Spec/Patch.lean`.
-/
