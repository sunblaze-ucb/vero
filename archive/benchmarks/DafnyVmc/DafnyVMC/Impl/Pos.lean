-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DafnyVMC.Impl.Pos

Foundation type `Pos` (strictly-positive natural numbers). This abbrev
is imported by every other DafnyVMC module that supplies positive-integer
arguments (e.g. sample bounds, Laplace/Gaussian scale parameters).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Foundation type (DO NOT MODIFY) ──────────────────────────────

/-- A strictly-positive natural number: a `Nat` together with a proof
    that it is greater than zero.  Corresponds to Dafny's `type pos`. -/
abbrev Pos := { n : Nat // n > 0 }
