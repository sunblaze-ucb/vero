-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eth20Dafny.Impl.Utils.Nonnativetypes

Foundation aliases for non-native unsigned integer widths used by the
Eth2.0 Dafny sources.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
-/


-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Eth20Dafny

-- ── Types (no markers — fixed vocabulary) ─────────────

/-- Dafny `uint128`, represented as a natural number in the benchmark model. -/
abbrev uint128 := Nat

/-- Dafny `uint256`, represented as a natural number in the benchmark model. -/
abbrev uint256 := Nat

end Eth20Dafny
