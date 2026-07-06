import DafnyVMC.Impl.Monad

/-!
# DafnyVMC.Spec.Monad

Specifications for the Hurd monad foundations.  The monad laws
(left unitality, right unitality, associativity) hold definitionally
for the reference implementations in `Impl/Monad.lean`; they do not
require separate `spec_*` entries at curation time.

`bitstreamsWithValueIn` and `bitstreamsWithRestIn` are vocabulary
helpers referenced by `DafnyVMC.Spec.Independence` and the
correctness specs — they live in `Impl/Monad.lean` and are
re-exported transitively through this import.

DO NOT MODIFY — this file is frozen curator-given content.
-/
